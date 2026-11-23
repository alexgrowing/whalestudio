import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicGoodModelDescent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanMatricesTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPlaceActionInjectiveStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.NoFixedFock

open Formalism.BasicNotions.TH GlobalTheory.RealLift

theorem oneFactor : ∀ (P Q R S : ℕ) (c : ℂ) (f : Formalism.BasicNotions.TH.Pol P Q R S), S < Q → c.re < ((R : ℝ) - S) / 2 →
    (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Y ∈ Formalism.BasicNotions.TH.upq P Q →
      Formalism.BasicNotions.TH.fockAct1 P Q R S Y f + (c * Y.trace) • f = 0) → f = 0 := GlobalTheory.T.fock_action_vanishing

theorem tensFactor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : Type) [AddCommGroup V] [Module ℂ V] (J : Type)
    (L : J → Module.End ℂ V) (w₀ : ι), (∀ v : V, (∀ j, L j v = 0) → v = 0) →
    ∀ T : ⨂[ℂ] _ : ι, V, (∀ j, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ (L j) T = 0) → T = 0 := GlobalTheory.T.tensor_place_action_injective

variable {F : Type} [Field F] [NumberField F]

theorem sa_of_acts {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) : SA T f f₁ := by
  intro g hg
  refine h (fun x => g (fun i => (x i).2)) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  change g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [fin_eq_zero_of_at hz, add_zero]

theorem atPl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (w : ι) :
    GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w 0 = 0 := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact (PiTensorProduct.tprod ℂ).map_coord_zero w (by simp)

end GlobalTheory.NoFixedFock

namespace GlobalTheory.NoFixedFock

open Formalism.BasicNotions.TH GlobalTheory.RealLift

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → G.q = 0 → 1 ≤ G.p →
      ∀ (M₁ : Model σ G.V W₁) (om₁ : Rep σ G.V W₁), M₁.IsGood B.ψ → M₁.IsWeil B.ψ X.β (X.β / X.α) om₁ →
        ∀ f ∈ M₁.Pol B.ψ B.emb, (∀ k ∈ KInf σ G.V B.emb, Acts (evI F) (om₁ (k, 1)) (⇑f) (⇑f)) → f = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' hq hp M₁ om₁ hM₁ hW f hf hfix
  classical
  have h := GlobalTheory.ThK.ComplPair.isPair_compl F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' hq hp M₁ om₁ hM₁ hW
  have hb := h.base
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.RealLift.FockFirst.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W₁.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.RealLift.FockFirst.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F W₁.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hsec : LieSecond := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hKP.base hder hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hKP.base hder hvl)
  have hfst : LieFirst := GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond hsec
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder hvl
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M₁.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ G.V W₁ M₁ B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F W₁.J) M₁.co X.β (X.β / X.α) om₁ := h.weil
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hact := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M₁.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (GlobalTheory.RealLift.FockFirst.hasExp_div B.emb hT.chars.expβ hT.chars.expα)
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf

  have key : ∀ Y : InfinitePlace F → Mat (a - G.p) G.p, (∀ w, IsKC (Y w) ∧ Y w ∈ upq (a - G.p) G.p) →
      sumPl (fun w => fockAct1 (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1) (Y w) +
        ((((B.mβ w - B.mα w : ℤ) : ℂ) / 2) * (Y w).trace) • 1) T = 0 := by
    intro Y hY
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) (a - G.p) G.p B.emb (incM F G.V.J) 1 A hb.cm
      hA1 Y (fun w => (hY w).2)
    have hK : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ KInf σ G.V B.emb := fun t => by
      refine ⟨hγ.2 _, fun w => ?_⟩
      obtain ⟨A', hAA⟩ := (hA w).2
      exact GlobalTheory.CompactLine.commute_of_gen (A w) A' hAA _ _ (Y w) (hY w).1 t (hAθ w) (hgen t w)
    have hSD := hact γ hγ Y hgen T
    have h0 : SD (fun t => (om₁.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t))) (Φ T) 0 := by
      intro g hg l hl
      have e : ∀ t : ℝ, (om₁.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g) = pureA F (Φ T) g :=
        fun t => sa_of_acts (hfix _ (hK t)) g hg
      have e0 : pureA F (⇑(0 : SInf F (Fin a × Fin d₁))) g = 0 := by
        funext x; simp [pureA]
      simp only [e, e0, map_zero]
      exact hasDerivAt_const _ _
    have e1 := (GlobalTheory.RealLift.actsLaws F (Fin a × Fin d₁) (Φ T) _ 0).2.2.2.2 _ hSD h0
    exact hΦ.1 (e1.trans (map_zero Φ).symm)
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set c : ℂ := ((B.mβ w₀ - B.mα w₀ : ℤ) : ℂ) / 2 with hcdef
  have hpa : G.p ≤ a := by have := (h.herm.sig w₀).1; omega
  have ha' : 1 ≤ a' := by have := hT.geo.aBig; omega
  have hk : ((a : ℝ) + a') < (B.mα w₀ : ℝ) - B.mβ w₀ := by
    have := hT.geo.kappa w₀
    have h2 : (((a + a' : ℕ) : ℤ) : ℝ) < ((B.mα w₀ - B.mβ w₀ : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    exact h2
  have hR : ((a + a' - G.p - 1 : ℕ) : ℝ) = (a : ℝ) + a' - G.p - 1 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  have hS : ((G.p - 1 : ℕ) : ℝ) = (G.p : ℝ) - 1 := by rw [Nat.cast_sub hp]; simp
  have hc : c.re = ((B.mβ w₀ : ℝ) - B.mα w₀) / 2 := by
    have e : c = ((((B.mβ w₀ : ℝ) - B.mα w₀) / 2 : ℝ) : ℂ) := by rw [hcdef]; push_cast; ring
    rw [e, Complex.ofReal_re]
  have hT0 : T = 0 := by
    refine tensFactor (InfinitePlace F) (Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1))
      {Y : Mat (a - G.p) G.p // IsKC Y ∧ Y ∈ upq (a - G.p) G.p}
      (fun j => fockAct1 (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1) j.1 + (c * j.1.trace) • 1) w₀ ?_ T ?_
    · intro v hv
      refine oneFactor _ _ _ _ c v (by omega) ?_ fun Y hY hY' => ?_
      · rw [hc, hR, hS]
        have : (G.p : ℝ) ≤ a := by exact_mod_cast hpa
        linarith
      · have := hv ⟨Y, hY, hY'⟩
        simpa using this
    · intro j
      have hj := key (fun w => if w = w₀ then j.1 else 0) (fun w => by
        split_ifs
        · exact j.2
        · exact ⟨fun _ _ _ => rfl, by simp [upq]⟩)
      have e : sumPl (fun w => fockAct1 (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1) (if w = w₀ then j.1 else 0) +
          ((((B.mβ w - B.mα w : ℤ) : ℂ) / 2) * (if w = w₀ then j.1 else 0).trace) • 1) =
          atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1)) w₀
            (fockAct1 (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1) j.1 + (c * j.1.trace) • 1) := by
        rw [sumPl, Finset.sum_eq_single w₀]
        · simp [hcdef]
        · intro w _ hw
          simp only [if_neg hw, map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero]
          exact atPl_zero w
        · intro h0; exact absurd (Finset.mem_univ w₀) h0
      rw [e] at hj
      exact hj
  rw [hT0, map_zero]

end GlobalTheory.NoFixedFock

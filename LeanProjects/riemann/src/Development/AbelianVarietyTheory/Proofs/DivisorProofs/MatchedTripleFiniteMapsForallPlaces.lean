import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaLie

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.FockAlg
open scoped Classical

theorem mem_span_of_sum_eq {X Y : Type} {m k : ℕ} (u : Fin m → X → ℂ) (hu : LinearIndependent ℂ u)
    (G : Fin m → Y → ℂ) (h : Fin k → X → ℂ) (g : Fin k → Y → ℂ) (π : Y → X)
    (hsplit : ∀ x y, ∃ y', π y' = x ∧ (∀ l, G l y' = G l y) ∧ ∀ j, g j y' = g j y)
    (hsum : ∀ y, ∑ l, u l (π y) * G l y = ∑ j, h j (π y) * g j y) (l : Fin m) :
    G l ∈ Submodule.span ℂ (Set.range g) := by
  by_contra hl
  obtain ⟨μ, hμ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hl inferInstance
  have hg : ∀ j, μ (g j) = 0 := fun j => by
    have : μ (g j) ∈ (Submodule.span ℂ (Set.range g)).map μ := ⟨g j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
    rw [hmap] at this
    exact this
  have hfun : ∀ x, ∑ l, u l x • G l = ∑ j, h j x • g j := fun x => by
    funext y
    obtain ⟨y', rfl, hG, hg'⟩ := hsplit x y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [← hG, ← hg']
    exact hsum y'
  have hzero : ∑ l, μ (G l) • u l = 0 := by
    funext x
    have := congrArg μ (hfun x)
    simp only [map_sum, map_smul, smul_eq_mul, hg, mul_zero, Finset.sum_const_zero] at this
    simpa [Finset.sum_apply, mul_comm] using this
  exact hμ (Fintype.linearIndependent_iff.1 hu _ hzero l)

theorem hasDerivAt_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : SD T f f₁)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (x : κ → AF F) :
    HasDerivAt (fun t => T t (pureA F f g) x) (pureA F f₁ g x) 0 := by
  have hl : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g' _ =>
    ⟨g' (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f' => by
      simp [pureA, mul_comm]⟩
  exact h g hg _ hl

theorem pure_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_der (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (γ : Multiplicative ℝ →* UA σ G.W.J)
    (hγ : γ ∈ Lines σ G.W) :
    ∃ D : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')),
      ∀ f ∈ G.M'.Pol B.ψ B.emb, D f ∈ G.M'.Pol B.ψ B.emb ∧
        SD (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (D f) := by
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hT
  choose A' hA' hAθ' using fun w => i_frameex _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1' : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A' w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA' w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr' : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A' C := ⟨one_mul _, hA1', hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hP i_derex hfe hvl (i_liescalar hP i_derex hvl)
  obtain ⟨Φ', hΦ'⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C hb.cm hb.std fr'
  have hr' := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A' C Φ' hb.cm hb.std fr' hAθ' hCθ hΦ'
  have hwp' : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hw'
  have hW2' := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C Φ' _ X.α B.mα hb.cm hb.std fr' hΦ' hwp'.1
    hc.expα
  obtain ⟨Yg, -, hY⟩ := i_genex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨Ψ', hΨ'⟩ := LinearMap.exists_leftInverse_of_injective Φ' (LinearMap.ker_eq_bot.2 hΦ'.1)
  refine ⟨Φ' ∘ₗ sumPl (fun w => fockAct2 _ _ _ _ (Yg w) + (((B.mα w : ℂ) / 2) * (Yg w).trace) • 1) ∘ₗ Ψ', fun f hf => ?_⟩
  obtain ⟨T, rfl⟩ := pol_eq B G.M' Φ' hr' hf
  have e : Ψ' (Φ' T) = T := by rw [← LinearMap.comp_apply, hΨ', LinearMap.id_apply]
  simp only [LinearMap.comp_apply, e]
  exact ⟨hr' ▸ LinearMap.mem_range_self _ _, hW2' γ hγ Yg hY T⟩

end GlobalTheory.ThetaLie

namespace GlobalTheory.ThetaLie

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.FockAlg
open scoped Classical

theorem lieClosed : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0 := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hm γ hγ Φ hΦ
  have hM' := hm.triple.geo.hM'
  obtain ⟨D, hD⟩ := exists_der hK.base hm.triple γ hγ
  obtain ⟨n, c, g, hgΦ⟩ := Submodule.mem_span_set'.1 hΦ.1
  choose f hf φ hφ hφv hgf using fun i => (g i).2
  have hf' : ∀ i, c i • f i ∈ G.M'.Pol B.ψ B.emb := fun i => Submodule.smul_mem _ _ (hf i)
  have hΦe : Φ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i) := by
    rw [← hgΦ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgf i, pure_smul]
  obtain ⟨k, c', g', hg'Φ⟩ := Submodule.mem_span_set'.1 hΦ.2
  choose h φ' hφ' hφ'v hφ'1 hg'h using fun j => (g' j).2
  have hΦe' : Φ = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c' j • h j) (φ' j) := by
    rw [← hg'Φ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg'h j, pure_smul]
  refine ⟨∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (D (c i • f i)) (φ i), ⟨?_, ?_⟩, fun x => ?_⟩
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨D (c i • f i), (hD _ (hf' i)).1, φ i, hφ i, hφv i, rfl⟩
  · let Wsp := Submodule.span ℂ (Set.range fun i => c i • f i)
    haveI : FiniteDimensional ℂ Wsp := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    let b := Module.finBasis ℂ Wsp
    let coeL : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] ((Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) → ℂ) :=
      { toFun := fun s => ⇑s, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have coeL_inj : Function.Injective coeL := fun s s' e => DFunLike.coe_injective e
    let aC : Fin n → Fin (Module.finrank ℂ Wsp) → ℂ := fun i l => b.repr ⟨c i • f i, Submodule.subset_span ⟨i, rfl⟩⟩ l
    have hexp : ∀ i, c i • f i = ∑ l, aC i l • (b l : SInf F (Fin a' × Fin (a + a'))) := fun i => by
      have e := congrArg Wsp.subtype (b.sum_repr ⟨c i • f i, Submodule.subset_span ⟨i, rfl⟩⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at e
      exact e.symm
    let π : (Fin a' × Fin (a + a') → AF F) → (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) := fun y i => evI F (y i)
    let r : Fin n → (Fin a' × Fin (a + a') → AF F) → ℂ := fun i y => ∏ᶠ v, φ i v fun j => evFin F v (y j)
    let r' : Fin k → (Fin a' × Fin (a + a') → AF F) → ℂ := fun j y => ∏ᶠ v, φ' j v fun i => evFin F v (y i)
    let Gf : Fin (Module.finrank ℂ Wsp) → (Fin a' × Fin (a + a') → AF F) → ℂ := fun l y => ∑ i, aC i l * r i y
    have hpure : ∀ (s : SInf F (Fin a' × Fin (a + a'))) i y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure s (φ i) y = s (π y) * r i y := fun _ _ _ => rfl
    have hpure' : ∀ (s : SInf F (Fin a' × Fin (a + a'))) j y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure s (φ' j) y = s (π y) * r' j y := fun _ _ _ => rfl
    have hev : ∀ (s : Fin (Module.finrank ℂ Wsp) → SInf F (Fin a' × Fin (a + a'))) (cs : Fin (Module.finrank ℂ Wsp) → ℂ) z,
        (∑ l, cs l • s l) z = ∑ l, cs l * s l z := by
      intro s cs z
      have := congrFun (map_sum coeL (fun l => cs l • s l) Finset.univ) z
      simpa [coeL, Finset.sum_apply] using this
    have key : ∀ L' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ y,
        ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (L' (c i • f i)) (φ i) y = ∑ l, L' (b l) (π y) * Gf l y := by
      intro L' y
      simp only [hpure, hexp, map_sum, map_smul, hev, Gf, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
    have hu : LinearIndependent ℂ (fun l => ((b l : SInf F (Fin a' × Fin (a + a'))) : (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) → ℂ)) :=
      b.linearIndependent.map' (coeL ∘ₗ Wsp.subtype)
        (LinearMap.ker_eq_bot.2 (coeL_inj.comp Subtype.val_injective))
    have hsplit : ∀ x y, ∃ y', π y' = x ∧ (∀ l, Gf l y' = Gf l y) ∧ ∀ j, r' j y' = r' j y := by
      intro x y
      refine ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (y i).2), ?_, fun l => rfl, fun j => rfl⟩
      funext i
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
    have hsum : ∀ y, ∑ l, (b l : SInf F (Fin a' × Fin (a + a'))) (π y) * Gf l y = ∑ j, (c' j • h j) (π y) * r' j y := by
      intro y
      have e1 := key LinearMap.id y
      simp only [LinearMap.id_apply] at e1
      have e2 : Φ y = ∑ l, (b l : SInf F (Fin a' × Fin (a + a'))) (π y) * Gf l y := by
        rw [hΦe, Finset.sum_apply]; exact e1
      have e3 : Φ y = ∑ j, (c' j • h j) (π y) * r' j y := by
        rw [hΦe', Finset.sum_apply]; rfl
      rw [← e2, e3]
    have hsep := mem_span_of_sum_eq _ hu Gf (fun j => ⇑(c' j • h j)) r' π hsplit hsum
    have hΦ1 : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (D (c i • f i)) (φ i)) = ∑ l, (fun y => D (b l) (π y) * Gf l y) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_apply, key D y]
    rw [hΦ1]
    refine Submodule.sum_mem _ fun l _ => ?_
    let Ms : ((Fin a' × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → AF F) → ℂ) :=
      { toFun := fun Gx y => D (b l) (π y) * Gx y
        map_add' := fun _ _ => by funext y; simp [mul_add]
        map_smul' := fun _ _ => by funext y; simp; ring }
    have hle : Submodule.span ℂ (Set.range r') ≤ (G.M'.So B.ψ B.τ₁).comap Ms := Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨D (b l), φ' j, hφ' j, hφ'v j, hφ'1 j, rfl⟩)
    exact hle (hsep l)
  · have e : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) =
        fun t => ∑ i, om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i)) x := by
      funext t
      rw [hΦe, map_sum, Finset.sum_apply]
    rw [e, Finset.sum_apply]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hsb := GlobalTheory.BigNZ.Fam.sb hM' (And.intro (hφ i) (hφv i))
    exact hasDerivAt_pureA (T := fun t => om' (1, γ (Multiplicative.ofAdd t))) (hD _ (hf' i)).2 hsb x

end GlobalTheory.ThetaLie

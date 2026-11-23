import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.InductLagr

theorem schr_add_mem {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (N : Submodule ℂ ((κ → K) → ℂ)) (a b : (κ → K) × (κ → K))
    (ha : ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ a φ ∈ N) (hb : ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ b φ ∈ N) :
    ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ (a + b) φ ∈ N := by
  intro φ hφ
  set c : K := ⅟(2 : K) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) with hc
  have law : GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) = ψ c • GlobalTheory.WeilM.schr ψ (a + b) φ := by
    funext x
    have key : (x ⬝ᵥ a.2 + ⅟(2 : K) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : K) * (b.1 ⬝ᵥ b.2)) =
        c + (x ⬝ᵥ (a + b).2 + ⅟(2 : K) * ((a + b).1 ⬝ᵥ (a + b).2)) := by
      have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
      simp only [hc, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
      linear_combination (-(a.1 ⬝ᵥ b.2)) * h2
    show ψ _ * (ψ _ * φ (x + a.1 + b.1)) = ψ c * (ψ _ * φ (x + (a + b).1))
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]
  have hne : ψ c ≠ 0 := by
    have h1 : ψ c * ψ (-c) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h1
  have e : GlobalTheory.WeilM.schr ψ (a + b) φ = (ψ c)⁻¹ • GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) := by
    rw [law, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact N.smul_mem _ (ha _ (hb _ hφ))

theorem exists_at_locCo {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = p := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)) :
        (κ → AF F) × (κ → AF F)) = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (p.1 k) r hr
      · exact GlobalTheory.LatVac.at_liftV v (p.2 k) r hr
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => GlobalTheory.LatVac.evFin_liftV v _) (funext fun k => GlobalTheory.LatVac.evFin_liftV v _)

end GlobalTheory.InductLagr

namespace GlobalTheory.InductLagr

theorem rel_of_vac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ {ι : Type} (P : Finset ι) (pl : ι → HeightOneSpectrum (𝓞 F)), Set.InjOn pl P →
    ∀ (Z : ι → Type) [∀ w, TopologicalSpace (Z w)] [∀ w, Add (Z w)]
      (A A' : ι → Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
      (co : ∀ w, Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z w)
      (I : ∀ w, ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ] (Z w → ℂ))
      (H : AddSubgroup (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
      (R : Submodule ℂ ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)))
      (f : SInf F (Fin n × Fin d)),
    (∀ w ∈ P, IsLagrModel M ψ (pl w) (A w) (A' w) (co w) (I w)) →
    (∀ w ∈ P, ∀ u ∈ A w, At (evFin F (pl w)) u ∧ u ∈ H) → (∀ w ∈ P, ∀ u ∈ A' w, At (evFin F (pl w)) u) →
    (∀ w ∈ P, ∀ u, At (evFin F (pl w)) u → ∃ x ∈ A w, ∃ y ∈ A' w, u = x + y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ u, co w (u + x) = co w u + co w x) →
    (∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x ∈ A w, ∀ u, co w' (u + x) = co w' u) →
    (∀ w ∈ P, ∀ u, ∃ x ∈ A w, co w x = co w u ∧ ∀ y ∈ A' w,
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y =
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ p ∈ R, (fun u => p.1 (u + x), M.co.rho ψ x p.2) ∈ R) →
    (∀ w ∈ P, ∀ y ∈ A' w, ∀ p ∈ R, (fun u => ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) * p.1 u, M.co.rho ψ y p.2) ∈ R) →
    (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) ∈ R →
    ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R := by
  intro F E _ _ _ _ _ σ n d X Y M ψ hstd hM ι P pl hpl Z _ _ A A' co I H R f hL hA hA' hdec hadd hloc hrep hRA hRA' hvac
  classical
  suffices key : ∀ S : Finset ι, S ⊆ P → ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, (∀ w ∈ S, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R by
    intro φ h1 h2
    exact key P subset_rfl φ h1 h2
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ φ _ h2
    have e : φ = M.vac := funext fun v => h2 v (by simp)
    subst e
    exact hvac
  | insert w S hwS ih =>
    intro hsub φ hφ1 hφ2
    have hwP : w ∈ P := hsub (Finset.mem_insert_self _ _)
    have hSP : S ⊆ P := (Finset.subset_insert _ _).trans hsub
    have hfam : GlobalTheory.BigNZ.Fam M φ := by
      refine ⟨hφ1, Filter.eventually_cofinite.2 (((insert w S).image pl).finite_toSet.subset fun v hv => ?_)⟩
      by_contra hc
      exact hv (hφ2 v fun w' hw' e => hc (Finset.mem_coe.2 (Finset.mem_image.2 ⟨w', hw', e⟩)))
    obtain ⟨r, -, er⟩ := GlobalTheory.PureFactor.exists_rest_factor (pl w) f φ (hfam.std hM)

    let C : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ := fun u => ∏ w' ∈ P.erase w, I w' (φ (pl w')) (co w' u)
    have hne : ∀ w' ∈ P.erase w, pl w' ≠ pl w := fun w' hw' e =>
      (Finset.mem_erase.1 hw').1 (hpl (Finset.mem_erase.1 hw').2 hwP e)
    have hprod : ∀ (χ : (Fin n × Fin d → Fv F (pl w)) → ℂ) u,
        ∏ w' ∈ P, I w' (Function.update φ (pl w) χ (pl w')) (co w' u) = I w χ (co w u) * C u := by
      intro χ u
      rw [← Finset.mul_prod_erase P _ hwP, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (hne w' hw')]

    let L : ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ]
        ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)) :=
      { toFun := fun χ => (Set.indicator (H : Set _) fun u => I w χ (co w u) * C u,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        map_add' := fun a b => Prod.ext (funext fun u => by
            by_cases hu : u ∈ (H : Set _)
            · simp only [Set.indicator_of_mem hu, map_add, Pi.add_apply, Prod.fst_add, add_mul]
            · simp only [Set.indicator_of_notMem hu, Prod.fst_add, Pi.add_apply, add_zero])
          (funext fun _ => add_mul _ _ _)
        map_smul' := fun c a => Prod.ext (funext fun u => by
            by_cases hu : u ∈ (H : Set _)
            · simp only [Set.indicator_of_mem hu, map_smul, Pi.smul_apply, Prod.smul_fst, smul_eq_mul,
                RingHom.id_apply, mul_assoc]
            · simp only [Set.indicator_of_notMem hu, Prod.smul_fst, Pi.smul_apply, smul_zero, RingHom.id_apply])
          (funext fun _ => mul_assoc _ _ _) }
    have hLe : ∀ χ, (Set.indicator (H : Set _) fun u => ∏ w' ∈ P, I w' (Function.update φ (pl w) χ (pl w')) (co w' u),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ (pl w) χ)) = L χ := fun χ =>
      Prod.ext (by simp only [hprod]; rfl) (er χ).symm
    let N : Submodule ℂ ((Fin n × Fin d → Fv F (pl w)) → ℂ) := GlobalTheory.WeilM.SB _ ⊓ R.comap L

    have hvacN : M.vac (pl w) ∈ N := by
      refine ⟨(hM.vac _).1, ?_⟩
      show L _ ∈ R
      rw [← hLe]
      refine ih hSP _ (fun v => ?_) (fun v hv => ?_)
      · by_cases e : v = pl w
        · subst e; rw [Function.update_self]; exact (hM.vac _).1
        · rw [Function.update_of_ne e]; exact hφ1 v
      · by_cases e : v = pl w
        · subst e; rw [Function.update_self]
        · rw [Function.update_of_ne e]
          refine hφ2 v fun w' hw' => ?_
          rcases Finset.mem_insert.1 hw' with h | h
          · subst h; exact fun e' => e e'.symm
          · exact hv w' h

    have hstA : ∀ x ∈ A w, ∀ χ ∈ N,
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.LatVac.locCo M.co (pl w) x) χ ∈ N := by
      intro x hx χ hχ
      obtain ⟨hxat, hxH⟩ := hA w hwP x hx
      have hsb := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 (pl w) (GlobalTheory.LatVac.locCo M.co (pl w) x) χ hχ.1
      have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ (pl w) x hxat χ
      refine ⟨hsb, ?_⟩
      show L _ ∈ R
      have hR := hRA w hwP x hx (L χ) hχ.2
      convert hR using 1
      refine Prod.ext (funext fun u => ?_) ?_
      · show Set.indicator (H : Set _) (fun u => I w _ (co w u) * C u) u =
          Set.indicator (H : Set _) (fun u => I w χ (co w u) * C u) (u + x)
        have hC : C (u + x) = C u := Finset.prod_congr rfl fun w' hw' => by
          rw [hloc w hwP w' (Finset.mem_of_mem_erase hw') (Finset.ne_of_mem_erase hw') x hx u]
        by_cases hu : u ∈ (H : Set _)
        · have hu' : u + x ∈ (H : Set _) := H.add_mem hu hxH
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu', hC, hadd w hwP x hx u,
            (hL w hwP).2.1 x hx χ hχ.1 _ hsb hact (co w u)]
        · have hu' : u + x ∉ (H : Set _) := fun h => hu (by simpa using H.sub_mem h hxH)
          rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
      · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) _ r = M.co.rho ψ x (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        rw [er, er, GlobalTheory.BigNZ.Fam.acts hM hfam f hχ.1 hact]

    have hstA' : ∀ y ∈ A' w, ∀ χ ∈ N,
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.LatVac.locCo M.co (pl w) y) χ ∈ N := by
      intro y hy χ hχ
      have hyat := hA' w hwP y hy
      have hsb := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 (pl w) (GlobalTheory.LatVac.locCo M.co (pl w) y) χ hχ.1
      have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ (pl w) y hyat χ
      refine ⟨hsb, ?_⟩
      show L _ ∈ R
      have hR := hRA' w hwP y hy (L χ) hχ.2
      convert hR using 1
      refine Prod.ext (funext fun u => ?_) ?_
      · show Set.indicator (H : Set _) (fun u => I w _ (co w u) * C u) u =
          ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) *
            Set.indicator (H : Set _) (fun u => I w χ (co w u) * C u) u
        by_cases hu : u ∈ (H : Set _)
        · obtain ⟨x, hx, hcx, hsx⟩ := hrep w hwP u
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← hcx,
            (hL w hwP).2.2 y hy χ hχ.1 _ hsb hact x hx, hsx y hy, mul_assoc]
        · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
      · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) _ r = M.co.rho ψ y (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        rw [er, er, GlobalTheory.BigNZ.Fam.acts hM hfam f hχ.1 hact]

    have hst : ∀ p, ∀ χ ∈ N, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) p χ ∈ N := by
      intro p χ hχ
      obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co (pl w) p
      obtain ⟨x, hx, y, hy, rfl⟩ := hdec w hwP u hu
      rw [map_add]
      exact schr_add_mem _ N _ _ (hstA x hx) (hstA' y hy) χ hχ
    have hN : N = GlobalTheory.WeilM.SB _ :=
      GlobalTheory.T.schroedinger_irreducible_finitePlaceCompletion (pl w) (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.SchrSB.continuous_psiAt ψ hstd.1 _)
        (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hstd _) N inf_le_left hst (M.vac (pl w)) hvacN (hM.vac _).2.1
    have hmem : φ (pl w) ∈ N := hN ▸ hφ1 (pl w)
    have h2 : L (φ (pl w)) ∈ R := hmem.2
    rw [← hLe, Function.update_eq_self] at h2
    exact h2

end GlobalTheory.InductLagr

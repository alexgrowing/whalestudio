import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

namespace GlobalTheory.LatCoordRed

open GlobalTheory.LevelActionPinned (sw SI)

variable {D : D7}

def crd (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (c : D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) : Fin V.rank → Lev.EAf D :=
  (c ⊗ₜ[D.host.F] (1 : Af D.host.F)) • ((β⁻¹).val *ᵥ fun j => sw D (z j))

theorem crd_add (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (c : D.host.E)
    (z z' : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    crd V β c (z + z') = crd V β c z + crd V β c z' := by
  have : (fun j => sw D ((z + z') j)) = (fun j => sw D (z j)) + fun j => sw D (z' j) := by
    funext j; simp
  rw [crd, crd, crd, this, Matrix.mulVec_add, smul_add]

theorem crd_nsmul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (c : D.host.E) (M : ℕ)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    crd V β c (M • z) = M • crd V β c z := by
  have : (fun j => sw D ((M • z) j)) = M • fun j => sw D (z j) := by
    funext j; simp
  rw [crd, crd, this, Matrix.mulVec_smul, smul_comm]

theorem crd_mulVec (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (c : D.host.E)
    {K : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    {Y : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)} (hK : K.map (sw D) = β.val * Y * (β⁻¹).val)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    crd V β c (K *ᵥ z) = Y *ᵥ crd V β c z := by
  rw [crd, crd, GlobalTheory.LevelActionPinned.equiv_mulVec, hK, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem crd_smul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (c b : D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    crd V β c (((1 : Af D.host.F) ⊗ₜ[D.host.F] b) • z) = (b ⊗ₜ[D.host.F] (1 : Af D.host.F)) • crd V β c z := by
  have : (fun j => sw D ((((1 : Af D.host.F) ⊗ₜ[D.host.F] b) • z) j)) =
      (b ⊗ₜ[D.host.F] (1 : Af D.host.F)) • fun j => sw D (z j) := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; rfl
  rw [crd, crd, this, Matrix.mulVec_smul, smul_comm]

theorem finVec_add (V : HSp D) (x y : Fin V.rank → D.host.E) : finVec V (x + y) = finVec V x + finVec V y := by
  funext i; simp [finVec, TensorProduct.tmul_add]

theorem finVec_smul (V : HSp D) (a : D.host.E) (x : Fin V.rank → D.host.E) :
    finVec V (a • x) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) • finVec V x := by
  funext i
  simp [finVec, Algebra.TensorProduct.tmul_mul_tmul]

theorem exists_scale (PP : Pl D.host.E) : ∃ c : D.host.E, (∀ a ∈ D.host.AA, ∃ x : 𝓞 D.host.E, (x : D.host.E) = c * a) ∧
    ∃ a₀ ∈ D.host.AA, ∃ e₀ : 𝓞 D.host.E, (e₀ : D.host.E) = c * a₀ ∧ e₀ - 1 ∈ PP.asIdeal := by
  classical
  have hI : D.host.AA ≠ 0 := GlobalTheory.SplitHomLattice.ideal_ne_zero D
  have h1 : D.host.AA⁻¹ * D.host.AA = 1 := inv_mul_cancel₀ hI
  have hint : ∀ c ∈ D.host.AA⁻¹, ∀ a ∈ D.host.AA, ∃ x : 𝓞 D.host.E, (x : D.host.E) = c * a := by
    intro c hc a ha
    have := FractionalIdeal.mul_mem_mul hc ha
    rw [h1] at this
    obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨x, hx⟩
  have hex : ∃ c ∈ D.host.AA⁻¹, ∃ a ∈ D.host.AA, ∃ x : 𝓞 D.host.E, (x : D.host.E) = c * a ∧ x ∉ PP.asIdeal := by
    by_contra hne
    push_neg at hne
    have hle : D.host.AA⁻¹ * D.host.AA ≤ (PP.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [FractionalIdeal.mul_le]
      intro c hc a ha
      obtain ⟨x, hx⟩ := hint c hc a ha
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x, hne c hc a ha x hx, hx⟩
    rw [h1, FractionalIdeal.one_le, FractionalIdeal.mem_coeIdeal] at hle
    obtain ⟨x, hx, hx1⟩ := hle
    have : x = 1 := RingOfIntegers.coe_injective (by simpa using hx1)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (this ▸ hx))
  obtain ⟨c, hc, a, ha, x, hx, hxP⟩ := hex
  obtain ⟨t, i, hi, hti⟩ := PP.isMaximal.exists_inv hxP
  refine ⟨c, hint c hc, (t : D.host.E) * a, ?_, t * x, ?_, ?_⟩
  · have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) t ha
    rwa [Algebra.smul_def] at this
  · have e : ((t * x : 𝓞 D.host.E) : D.host.E) = (t : D.host.E) * (x : D.host.E) := rfl
    rw [e, hx]; ring
  · have e : t * x - 1 = -i := by rw [← hti]; ring
    rw [e]; exact neg_mem hi

theorem crd_mem {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {c : D.host.E} (hc : ∀ a ∈ D.host.AA, ∃ x : 𝓞 D.host.E, (x : D.host.E) = c * a) :
    ∀ w ∈ latGHat V 1, ∀ i, crd V β c w i ∈ SI D := by
  intro w hw
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩ := hw
    intro i
    obtain ⟨x, hx⟩ := hc a ha
    rw [crd_smul]
    have h1 := (GlobalTheory.LevelActionPinned.mem_latHat_iff hβ z).1 hz i
    have h2 := (oToS D.host.F D.host.E x).2
    rw [oToS_coe] at h2
    show (a ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((c ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((β⁻¹).val *ᵥ fun j => sw D (z j)) i) ∈ SI D
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm a c, ← hx]
    exact mul_mem h2 h1
  | zero =>
    intro i
    have e : (fun j => sw D ((0 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) j)) = 0 := by funext j; simp
    rw [crd, e, Matrix.mulVec_zero, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy => intro i; rw [crd_add]; exact add_mem (hx i) (hy i)
  | neg x _ hx =>
    intro i
    have : crd V β c (-x) = -crd V β c x := by
      have e : (fun j => sw D ((-x) j)) = -fun j => sw D (x j) := by funext j; simp
      rw [crd, crd, e, Matrix.mulVec_neg, smul_neg]
    rw [this]; exact neg_mem (hx i)

theorem exists_approx (V : HSp D) (N : ℕ) (hN : N ≠ 0) :
    ∀ z ∈ latGHat V 1, ∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, z = finVec V x + N • w := by
  have h0 : finVec V 0 = 0 := by funext i; simp [finVec]
  have hneg : ∀ x, finVec V (-x) = -finVec V x := by intro x; funext i; simp [finVec, TensorProduct.tmul_neg]
  have P0 : ∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, (0 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) = finVec V x + N • w :=
    ⟨0, zero_mem _, 0, zero_mem _, by rw [h0, smul_zero, add_zero]⟩
  have Padd : ∀ z z', (∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, z = finVec V x + N • w) →
      (∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, z' = finVec V x + N • w) →
      ∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, z + z' = finVec V x + N • w := by
    rintro z z' ⟨x, hx, w, hw, rfl⟩ ⟨x', hx', w', hw', rfl⟩
    refine ⟨x + x', add_mem hx hx', w + w', add_mem hw hw', ?_⟩
    rw [finVec_add, smul_add]; abel
  have Pneg : ∀ z, (∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, z = finVec V x + N • w) →
      ∃ x ∈ latG V 1, ∃ w ∈ latGHat V 1, -z = finVec V x + N • w := by
    rintro z ⟨x, hx, w, hw, rfl⟩
    refine ⟨-x, neg_mem hx, -w, neg_mem hw, ?_⟩
    rw [hneg, smul_neg, neg_add]
  intro z hz
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩ := hz
    unfold latHat at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hz
      obtain ⟨r, y, hy, hby⟩ := Formalism.UG.P.integral_adele_approximation_holds D.host.F (N : 𝓞 D.host.F) (by exact_mod_cast hN) b hb
      set u : Fin V.rank → D.host.E := fun i => V.frame.repr x i with hu
      have hv : finVec V u ∈ gLat V 1 := by
        refine ⟨_, AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩, ?_⟩
        rw [map_one, Units.val_one, Matrix.one_mulVec]
        rfl
      have hau : a • u ∈ latG V 1 := Submodule.subset_span ⟨a, ha, u, hv, rfl⟩
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (a • u), Submodule.smul_mem _ _ hau,
        ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) • (fun i => y ⊗ₜ[D.host.F] u i), ?_, ?_⟩
      · rw [GlobalTheory.LevelActionPinned.latGHat_one]
        exact AddSubgroup.subset_closure ⟨_, ⟨a, ha, rfl⟩, _, AddSubgroup.subset_closure ⟨y, hy, x, hx, rfl⟩, rfl⟩
      · funext i
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, finVec, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hby, hu]
        rw [TensorProduct.add_tmul]
        congr 1
        · rw [IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F),
            Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, algebraMap_smul, algebraMap_smul]
        · rw [map_natCast, ← nsmul_eq_mul, TensorProduct.smul_tmul']
    | zero => simpa only [smul_zero] using P0
    | add z z' _ _ hz hz' => rw [smul_add]; exact Padd _ _ hz hz'
    | neg z _ hz => rw [smul_neg]; exact Pneg _ hz
  | zero => exact P0
  | add z z' _ _ hz hz' => exact Padd _ _ hz hz'
  | neg z _ hz => exact Pneg _ hz

theorem exists_of_coords {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {c a₀ : D.host.E} (ha₀ : a₀ ∈ D.host.AA) {e₀ : 𝓞 D.host.E} (he₀ : (e₀ : D.host.E) = c * a₀)
    (v : Fin V.rank → 𝓞 D.host.E) :
    ∃ z ∈ latGHat V 1, ∀ i, crd V β c z i = (oToS D.host.F D.host.E (e₀ * v i) : Lev.EAf D) := by
  let o : Fin V.rank → Lev.EAf D := fun j => (oToS D.host.F D.host.E (v j) : Lev.EAf D)
  let z0 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E := fun i => (sw D).symm ((β.val *ᵥ o) i)
  have hsw : (fun j => sw D (z0 j)) = β.val *ᵥ o := by funext j; simp [z0]
  have hβo : (β⁻¹).val *ᵥ (β.val *ᵥ o) = o := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hz0 : z0 ∈ latHat V := by
    rw [GlobalTheory.LevelActionPinned.mem_latHat_iff hβ]
    intro i
    rw [hsw, hβo]
    exact (oToS D.host.F D.host.E (v i)).2
  refine ⟨((1 : Af D.host.F) ⊗ₜ[D.host.F] a₀) • z0, ?_, fun i => ?_⟩
  · rw [GlobalTheory.LevelActionPinned.latGHat_one]
    exact AddSubgroup.subset_closure ⟨_, ⟨a₀, ha₀, rfl⟩, z0, hz0, rfl⟩
  · rw [crd_smul]
    show (a₀ ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((c ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((β⁻¹).val *ᵥ fun j => sw D (z0 j)) i) = _
    rw [hsw, hβo, map_mul, Subring.coe_mul, oToS_coe, oToS_coe, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 2
    rw [mul_comm]; exact he₀.symm

theorem natCast_kP (PP : Pl D.host.E) {M : ℕ} (hM : (M : 𝓞 D.host.E) ∈ PP.asIdeal) : (M : kP PP) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hM

theorem resS_combo (PP : Pl D.host.E) {n : ℕ} (s t : Fin n → SI D) (u : SI D) {M : ℕ}
    (hM : (M : 𝓞 D.host.E) ∈ PP.asIdeal) :
    resS D.host.F PP (∑ j, s j * t j + M • u) = ∑ j, resS D.host.F PP (s j) * resS D.host.F PP (t j) := by
  rw [map_add, map_nsmul, nsmul_eq_mul, natCast_kP PP hM, zero_mul, add_zero, map_sum]
  simp only [map_mul]

theorem coord_red : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ φ : La →ₗ[𝓞 D.host.E] (Fin V.rank → kP PP), Function.Surjective φ ∧ ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ a b : La, (∃ w ∈ latGHat V 1, finVec V (ι b) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w) → φ b = (redFn β PP (Lev.finE V k)).1.mulVec (φ a) := by
  intro D V β Λ hβ La _ _ ι hι PP
  obtain ⟨c, hc, a₀, ha₀, e₀, he₀, he₀1⟩ := exists_scale (D := D) PP
  have hmem : ∀ a : La, finVec V (ι a) ∈ latGHat V 1 := fun a =>
    ((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1 (hι.2 ▸ LinearMap.mem_range_self ι a)
  have hint := crd_mem hβ hc
  let φ : La →ₗ[𝓞 D.host.E] (Fin V.rank → kP PP) :=
    { toFun := fun a i => resS D.host.F PP ⟨crd V β c (finVec V (ι a)) i, hint _ (hmem a) i⟩
      map_add' := by
        intro a b
        funext i
        simp only [Pi.add_apply]
        rw [← map_add]
        congr 1
        apply Subtype.ext
        simp only [map_add, finVec_add, crd_add, Pi.add_apply, Subring.coe_add]
      map_smul' := by
        intro b a
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Algebra.smul_def]
        show _ = Ideal.Quotient.mk PP.asIdeal b * _
        rw [← resS_oToS (F := D.host.F), ← map_mul]
        congr 1
        apply Subtype.ext
        show crd V β c (finVec V (ι (b • a))) i = (oToS D.host.F D.host.E b : Lev.EAf D) * crd V β c (finVec V (ι a)) i
        have hb : b • ι a = (b : D.host.E) • ι a := by
          funext j; simp [Algebra.smul_def]
        rw [map_smul, hb, finVec_smul, crd_smul, oToS_coe]
        rfl }
  refine ⟨φ, ?_, ?_⟩
  · intro v
    choose v' hv' using fun i => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (v i)
    obtain ⟨z, hz, hcz⟩ := exists_of_coords hβ ha₀ he₀ v'
    have hN0 : Ideal.absNorm PP.asIdeal ≠ 0 := fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    obtain ⟨x, hx, w, hw, hzx⟩ := exists_approx V _ hN0 z hz
    obtain ⟨a, rfl⟩ : x ∈ LinearMap.range ι := hι.2 ▸ hx
    refine ⟨a, funext fun i => ?_⟩
    have hN : ((Ideal.absNorm PP.asIdeal : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Ideal.absNorm_mem _
    have e : (⟨crd V β c (finVec V (ι a)) i, hint _ (hmem a) i⟩ : SI D) =
        oToS D.host.F D.host.E (e₀ * v' i) - (Ideal.absNorm PP.asIdeal : ℕ) • ⟨crd V β c w i, hint _ hw i⟩ := by
      apply Subtype.ext
      have h2 : crd V β c z i = crd V β c (finVec V (ι a)) i + (Ideal.absNorm PP.asIdeal : ℕ) • crd V β c w i := by
        rw [hzx, crd_add, crd_nsmul]; rfl
      show crd V β c (finVec V (ι a)) i = _
      push_cast
      rw [← hcz i, h2]
      abel
    show resS D.host.F PP ⟨crd V β c (finVec V (ι a)) i, hint _ (hmem a) i⟩ = v i
    have he1 : Ideal.Quotient.mk PP.asIdeal e₀ = 1 := by
      rw [← map_one (Ideal.Quotient.mk PP.asIdeal)]; exact Ideal.Quotient.eq.2 he₀1
    rw [e, map_sub, map_nsmul, resS_oToS, map_mul, hv' i, he1, one_mul, nsmul_eq_mul, natCast_kP PP hN, zero_mul,
      sub_zero]
  · intro k hk M hM a b ⟨w, hw, e⟩
    obtain ⟨y, hy⟩ := hk
    have hK := GlobalTheory.LevelActionPinned.map_finHom hy
    rw [← hy, redFn_frGL]
    funext i
    have e' : finVec V (ι b) = (finHom V k).1 *ᵥ finVec V (ι a) + M • w := by rw [← e]; abel
    have e2 : (⟨crd V β c (finVec V (ι b)) i, hint _ (hmem b) i⟩ : SI D) =
        ∑ j, y.val i j * ⟨crd V β c (finVec V (ι a)) j, hint _ (hmem a) j⟩ + M • ⟨crd V β c w i, hint _ hw i⟩ := by
      apply Subtype.ext
      show crd V β c (finVec V (ι b)) i = _
      rw [e', crd_add, crd_nsmul, crd_mulVec V β c hK]
      push_cast
      rfl
    show resS D.host.F PP ⟨crd V β c (finVec V (ι b)) i, hint _ (hmem b) i⟩ =
      ∑ j, resS D.host.F PP (y.val i j) * resS D.host.F PP ⟨crd V β c (finVec V (ι a)) j, hint _ (hmem a) j⟩
    rw [e2]
    exact resS_combo PP _ _ _ hM

end GlobalTheory.LatCoordRed

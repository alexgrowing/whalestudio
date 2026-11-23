import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PResClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot galTot galTotRep pullTot_comp)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.EtaleTowerBaseChange

section Lin
variable {R : Type*} [CommSemiring R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

private theorem lmap_pow_lof [DecidableEq ι] (G : ∀ i, Module.End R (M i)) (m : ℕ) (k : ι) (x : M k) :
    ((DirectSum.lmap G : Module.End R (DirectSum ι fun i => M i)) ^ m) (DirectSum.lof R ι M k x) =
      DirectSum.lof R ι M k ((G k ^ m) x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, DirectSum.lmap_lof, pow_succ', Module.End.mul_apply]

private theorem directSum_lmap_pow_apply (G : ∀ i, Module.End R (M i)) (m : ℕ) (x : DirectSum ι fun i => M i) (i : ι) :
    ((DirectSum.lmap G : Module.End R (DirectSum ι fun i => M i)) ^ m) x i = (G i ^ m) (x i) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, ih, DirectSum.lmap_apply, pow_succ, Module.End.mul_apply]

private theorem lmap_sum_zero {J : Type*} [Fintype J] (c : J → R) (A : J → ∀ i, Module.End R (M i))
    (G : ∀ i, Module.End R (M i)) (e : J → ℕ) (h : ∀ k, ∑ j, c j • (A j k * G k ^ e j) = 0) :
    ∑ j, c j • ((DirectSum.lmap (A j) : Module.End R (DirectSum ι fun i => M i)) *
      (DirectSum.lmap G : Module.End R (DirectSum ι fun i => M i)) ^ e j) = 0 := by
  refine LinearMap.ext fun x => DFinsupp.ext fun i => ?_
  have hk := congrArg (fun f : Module.End R (M i) => f (x i)) (h i)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.zero_apply] at hk ⊢
  rw [DFinsupp.finset_sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hk
  rw [DFinsupp.smul_apply, DirectSum.lmap_apply, directSum_lmap_pow_apply]

end Lin

section Core
variable {Q L A B : Type*} [Field Q] [Field L] [Algebra Q L] [CharZero L]
  [AddCommGroup A] [Module Q A] [AddCommGroup B] [Module Q B]

private theorem bc_comm (P : B →ₗ[Q] A) (G : A →ₗ[Q] A) (G' : B →ₗ[Q] B) (h : ∀ x, P (G' x) = G (P x))
    (y : L ⊗[Q] B) : P.baseChange L (G'.baseChange L y) = G.baseChange L (P.baseChange L y) := by
  have hc : P ∘ₗ G' = G ∘ₗ P := LinearMap.ext h
  have hb := congrArg (fun f : B →ₗ[Q] A => f.baseChange L y) hc
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using hb

private theorem bc_iter (P : B →ₗ[Q] A) (G : A →ₗ[Q] A) (G' : B →ₗ[Q] B) (h : ∀ x, P (G' x) = G (P x))
    (k : ℕ) (y : L ⊗[Q] B) :
    (G.baseChange L)^[k] (P.baseChange L y) = P.baseChange L ((G'.baseChange L)^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← bc_comm P G G' h, ih]

private theorem bc_pow (G' : Module.End Q B) (k : ℕ) (y : L ⊗[Q] B) :
    LinearMap.baseChange L (G' ^ k) y = (G'.baseChange L)^[k] y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← ih, pow_succ, Module.End.mul_eq_comp, LinearMap.baseChange_comp,
      LinearMap.comp_apply]

private theorem core {n : ℕ} (P : B →ₗ[Q] A) (G : A →ₗ[Q] A) (G' : Module.End Q B)
    (hG : ∀ x, P (G' x) = G (P x)) (Hh : Fin (n + 1) → A →ₗ[Q] A) (T : Fin (n + 1) → Module.End Q B)
    (m : Fin (n + 1) → ℕ) (hm : ∀ j, m j ≠ 0) (hH : ∀ j, Hh j ∘ₗ P = (m j : Q) • (P ∘ₗ T j))
    (c : Fin (n + 1) → ℤ) (ϑ : Fin (n + 1) → L) (h0 : ∑ j : Fin (n + 1), (c j : Q) • (T j * G' ^ (n - (j : ℕ))) = 0)
    (U : Submodule L (L ⊗[Q] A)) (hU : ∀ x ∈ U, G.baseChange L x ∈ U)
    (hUe : ∀ j, ∀ x ∈ U, (Hh j).baseChange L x = ((m j : L) * ϑ j) • x)
    (y : L ⊗[Q] B) (hx : P.baseChange L y ∈ U) :
    ∑ j : Fin (n + 1), ((c j : L) * ϑ j) • (G.baseChange L)^[n - (j : ℕ)] (P.baseChange L y) = 0 := by
  have hw : ∀ k : ℕ, (G.baseChange L)^[k] (P.baseChange L y) ∈ U := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hU _ ih
  have key : ∀ j : Fin (n + 1), ϑ j • (G.baseChange L)^[n - (j : ℕ)] (P.baseChange L y) =
      P.baseChange L ((T j * G' ^ (n - (j : ℕ))).baseChange L y) := by
    intro j
    have hne : ((m j : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (hm j)
    apply smul_right_injective (L ⊗[Q] A) hne
    dsimp only
    have e1 := hUe j _ (hw (n - (j : ℕ)))
    rw [bc_iter P G G' hG] at e1
    have e2 := congrArg (fun f : B →ₗ[Q] A => f.baseChange L ((G'.baseChange L)^[n - (j : ℕ)] y)) (hH j)
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.baseChange_smul,
      LinearMap.smul_apply] at e2
    rw [smul_smul, bc_iter P G G' hG, ← e1, e2, Nat.cast_smul_eq_nsmul Q, Nat.cast_smul_eq_nsmul L,
      LinearMap.baseChange_mul, Module.End.mul_apply, bc_pow]
  have hz : (∑ j : Fin (n + 1), (c j : Q) • (T j * G' ^ (n - (j : ℕ)))).baseChange L y = 0 := by
    rw [h0, LinearMap.baseChange_zero, LinearMap.zero_apply]
  have hs := congrArg (P.baseChange L) hz
  rw [map_zero] at hs
  rw [← hs]
  have hsum := map_sum (LinearMap.baseChangeHom Q L B B)
    (fun j : Fin (n + 1) => (c j : Q) • (T j * G' ^ (n - (j : ℕ)))) Finset.univ
  simp only [LinearMap.baseChangeHom_apply] at hsum
  rw [hsum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul, key j, LinearMap.baseChange_smul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul Q, map_zsmul,
    Int.cast_smul_eq_zsmul L]

end Core

section Geo
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

private theorem gm_fst {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := by
  unfold geomMap
  exact pullback.lift_fst _ _ _

private theorem gm_snd {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold geomMap
  exact pullback.lift_snd _ _ _

private theorem gm_gal {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) : geomMap Ω p u hu ≫ galMap Ω q σ = galMap Ω p σ ≫ geomMap Ω p u hu := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, galMap_fst, gm_fst Ω p u hu, galMap_fst_assoc]
  · rw [Category.assoc, Category.assoc, galMap_snd, gm_snd Ω p u hu, ← Category.assoc, gm_snd Ω p u hu,
      galMap_snd]

end Geo

private theorem pi_gal (l : ℕ) [Fact l.Prime] {k L : Type} [Field k] [Field L] {H : HTower k} {θ : H.Γ → L} {O : Type}
    [CommRing O] [Algebra O k] (C : Cover H θ O) (Ω : Type) [Field Ω] [Algebra k Ω] (τ : Ω ≃ₐ[k] Ω)
    (x : Htot l (sch.obj (geom Ω (pullback.snd C.p (sp (algebraMap O k)))))) :
    pullTot l (sch.map (piG C Ω)) (galTot l Ω (pullback.snd C.p (sp (algebraMap O k))) τ x) =
      galTot l Ω H.q τ (pullTot l (sch.map (piG C Ω)) x) := by
  have e : piG C Ω ≫ galMap Ω (pullback.snd C.p (sp (algebraMap O k))) τ = galMap Ω H.q τ ≫ piG C Ω :=
    gm_gal Ω _ _ _ τ
  have e2 := congrArg (fun f => pullTot l (sch.map f) x) e
  simp only [Functor.map_comp, pullTot_comp, LinearMap.comp_apply] at e2
  simpa only [galTot] using e2

end UpperTheory.Gal.Mod.EtaleTowerBaseChange

open UpperTheory.Gal.Mod.EtaleTowerBaseChange in
theorem UpperTheory.Gal.Mod.towES :
    ESGen → BCEx → LiesOp → FixDesc → TowES := by
  intro hES hBC hLies hFix l _ p f n hp O _ _ _ hpu K _ _ hp0 hres Ω _ _ _ V hV hmax hlv L _ _ H θ hN C ϑ hC
    hstab σ hσ x hx
  obtain ⟨ϖ, T, γ, m, hϖ, hpt, hj⟩ := hC
  have hlΩ : IsUnit (l : Ω) := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, map_zero] at hlv
    exact zero_ne_one hlv
  obtain ⟨y, rfl⟩ := hFix l K L H θ O C Ω hlΩ x hx
  choose c hc using fun j : Fin (n + 1) => hBC p O K Ω hp0 C.Y C.p (T j) (hj j).1
  haveI : IsProper C.p := GlobalTheory.ProperFamily.isProper_of_isProjOver C.proj
  haveI : Smooth C.p := C.smooth
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  let f0 : O →+* V := ((algebraMap K Ω).comp (algebraMap O K)).codRestrict V.toSubring hV
  haveI : IsLocalHom f0 := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna)
    have h1 := (V.valuation_eq_one_iff (f0 a)).mp ha
    have h2 := hmax a hm
    exact absurd h1 (ne_of_lt h2)
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField V) :=
    (IsLocalRing.ResidueField.map f0).toAlgebra
  haveI : IsAlgClosed (FractionRing V) :=
    IsAlgClosed.of_ringEquiv Ω _ (FractionRing.algEquiv V Ω).symm.toRingEquiv
  haveI : IsAlgClosed (IsLocalRing.ResidueField V) := resClosed V
  have hκ : algebraMap O (IsLocalRing.ResidueField O) ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
  have hrc : ∀ a : O, IsLocalRing.residue V ⟨algebraMap K Ω (algebraMap O K a), hV a⟩ =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField V)
        (algebraMap O (IsLocalRing.ResidueField O) a) :=
    fun a => (IsLocalRing.ResidueField.map_residue f0 a).symm
  have hlV : IsUnit (l : V) := (V.valuation_eq_one_iff _).mpr (by exact_mod_cast hlv)
  have hlk : IsUnit (l : IsLocalRing.ResidueField V) := by
    simpa using hlV.map (IsLocalRing.residue V)
  have key := fun k : ℤ => hES l p f n hp O ϖ hϖ hpu K (IsLocalRing.ResidueField O) hp0 hκ hres Ω V hV
    (IsLocalRing.ResidueField V) (IsLocalRing.residue V) IsLocalRing.residue_surjective hrc hlk C.Y C.p T
    (fun j => (hj j).1) hpt c hc σ hσ k
  refine ⟨fun hσ1 => ?_, fun hσ2 => ?_⟩
  · have hr1 : ∀ v : V, IsLocalRing.residue V ⟨σ v, hσ v v.2⟩ = IsLocalRing.residue V v := by
      intro v
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, V.valuation_lt_one_iff]
      exact hσ1 v v.2
    have hg : galTot l Ω (pullback.snd C.p (sp (algebraMap O K))) σ = 1 := by
      show DirectSum.lmap (fun k => galHQ l Ω (pullback.snd C.p (sp (algebraMap O K))) k 0 σ) = 1
      rw [show (fun k => galHQ l Ω (pullback.snd C.p (sp (algebraMap O K))) k 0 σ) = fun k => LinearMap.id
        from funext fun k => (key k).1 hr1]
      exact DirectSum.lmap_id
    show (galTot l Ω H.q σ).baseChange L _ = _
    rw [← bc_comm _ _ _ (pi_gal l C Ω σ) y, hg, LinearMap.baseChange_one, Module.End.one_apply]
  · have hr2 : ∀ v : V, IsLocalRing.residue V ⟨σ v, hσ v v.2⟩ = IsLocalRing.residue V v ^ p ^ f := by
      intro v
      rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, V.valuation_lt_one_iff]
      exact hσ2 v v.2
    have h0 := lmap_sum_zero (R := ℚ_[l]) (fun j : Fin (n + 1) => ((co (p ^ f) j : ℤ) : ℚ_[l]))
      (fun j k => TranscendenceTraces.Corr.opQ l (c j) k 0)
      (fun k => galHQ l Ω (pullback.snd C.p (sp (algebraMap O K))) k 0 σ⁻¹) (fun j => n - (j : ℕ))
      (fun k => (key k).2 hr2)
    have hd : ∀ j, ∃ d, FEt (H.s (γ j)) d := fun j => hN.2.2 (γ j)
    choose d hd using hd
    have hH := fun j => hLies l p K L H θ O C Ω hlΩ (T j) (γ j) (d j) (m j) (hd j) (hj j).2.1 (c j) (hc j)
    have hUe : ∀ j, ∀ z ∈ piece l H Ω L θ,
        (hop l H Ω (γ j)).baseChange L z = ((m j : L) * ϑ j) • z := by
      intro j z hz
      have hz' : z ∈ ⨅ g, Module.End.eigenspace ((hop l H Ω g).baseChange L) (θ g) := hz
      have := (Submodule.mem_iInf _).mp hz' (γ j)
      rw [Module.End.mem_eigenspace_iff] at this
      rw [this, (hj j).2.2]
    exact core (pullTot l (sch.map (piG C Ω))) (galTot l Ω H.q σ⁻¹)
      (galTot l Ω (pullback.snd C.p (sp (algebraMap O K))) σ⁻¹) (pi_gal l C Ω σ⁻¹)
      (fun j => hop l H Ω (γ j)) (fun j => DirectSum.lmap fun k => TranscendenceTraces.Corr.opQ l (c j) k 0) m
      (fun j => ((hj j).2.1.1).ne') hH (fun j => co (p ^ f) j) (fun j => ϑ j) h0 (piece l H Ω L θ)
      (fun z hz => hstab σ⁻¹ z hz) hUe y hx

import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.Published

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsPlacesIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) : Prop :=
  (∀ w ∈ S₁, fstA F ε w = 1) ∧ (∀ w, w ∉ S₁ → fstA F ε w = 0) ∧
    (∀ v ∈ S₂, evalV F v (sndA F ε) = 1) ∧ (∀ v, v ∉ S₂ → evalV F v (sndA F ε) = 0)

def SUAdelic (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) :=
  (Matrix.GeneralLinearGroup.det.comp (HR (AF F) σ J).subtype).ker

def SURat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) :=
  SUAdelic σ J ⊓ (HFinIn (AF F) σ J : Subgroup (HA (AF F) σ J))

def SUSupp (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) : Set (HA (AF F) σ J) :=
  {g | g ∈ SUAdelic σ J ∧ ∀ i j,
    algebraMap (AF F) (AF F ⊗[F] E) ε * (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j =
      (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j}

end Defs

def StrongApproxSU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J →
    ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
      ¬ IsCompact (SUSupp σ J ε) →
      ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}

namespace StrongApprox

section Ring

open Matrix Formalism.UG

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def elt (J K : Matrix n n R) (i j : n) (a b : R) : Matrix n n R :=
  1 + a • single i j (1 : R) - b • (K * single j i (1 : R) * J)

theorem det_elt {J K : Matrix n n R} (hKJ : K * J = 1) {i j : n} (hij : i ≠ j) {a b : R} (hab : a * b = 0) :
    (elt J K i j a b).det = 1 := by
  have e : elt J K i j a b = transvection i j a * (K * transvection j i (-b) * J) := by
    have h1 : single i j a = a • single i j (1 : R) := by simp
    have h2 : single j i (-b) = (-b) • single j i (1 : R) := by rw [smul_single, smul_eq_mul, mul_one]
    unfold elt transvection
    rw [h1, h2]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, hKJ,
      smul_smul, smul_add]
    rw [show -b * a = 0 by rw [neg_mul, mul_comm, hab, neg_zero], zero_smul, add_zero, neg_smul]
    abel
  rw [e, det_mul, det_mul, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, one_mul,
    mul_one, ← det_mul, hKJ, det_one]

theorem unitary_elt (c : R →+* R) {J K : Matrix n n R} (hJ : cT c J = J) (hKJ : K * J = 1) (hJK : J * K = 1)
    {i j : n} (hij : i ≠ j) {a b : R} (hab : a * b = 0) (hca : c a = b) (hcb : c b = a) :
    cT c (elt J K i j a b) * J * elt J K i j a b = J := by
  have hK : cT c K = K := by
    have h : cT c K * J = 1 := by rw [← hJ, ← cT_mul, hJK, cT_one]
    calc cT c K = cT c K * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  have hs : ∀ p q : n, cT c (single p q (1 : R)) = single q p 1 := by
    intro p q
    ext x y
    simp only [cT, transpose_apply, map_apply, single_apply]
    by_cases h : p = y ∧ q = x
    · rw [if_pos h, if_pos h.symm, map_one]
    · rw [if_neg h, if_neg (fun h' => h h'.symm), map_zero]
  have h1 : cT c (elt J K i j a b) = 1 + b • single j i (1 : R) - a • (J * single i j (1 : R) * K) := by
    have : J * single i j (1 : R) * K = cT c (K * single j i (1 : R) * J) := by
      rw [cT_mul, cT_mul, hJ, hK, hs, Matrix.mul_assoc]
    have hgen : ∀ X Y Z : Matrix n n R, cT c (X + a • Y - b • Z) = cT c X + b • cT c Y - a • cT c Z := by
      intro X Y Z
      ext x y
      simp [cT, hca, hcb]
    rw [this, elt, hgen, cT_one, hs i j]
  set N := single i j (1 : R) with hN
  set N' := single j i (1 : R) with hN'
  have hNN : N * N = 0 := single_mul_single_of_ne _ _ _ _ hij.symm _
  have hNN' : N' * N' = 0 := single_mul_single_of_ne _ _ _ _ hij _
  have h2 : cT c (elt J K i j a b) * J = J + b • (N' * J) - a • (J * N) := by
    rw [h1]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, hKJ,
      Matrix.mul_one]
  have h3 : J * (K * N' * J) = N' * J := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJK, Matrix.one_mul]
  have h4 : N' * J * (K * N' * J) = 0 := by
    rw [Matrix.mul_assoc, h3, ← Matrix.mul_assoc, hNN', Matrix.zero_mul]
  have h5 : J * N * N = 0 := by rw [Matrix.mul_assoc, hNN, Matrix.mul_zero]
  have hba : b * a = 0 := by rw [mul_comm, hab]
  rw [h2]
  unfold elt
  rw [← hN, ← hN']
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h3, h4, h5, smul_add, smul_sub, smul_smul, hab, hba, zero_smul, smul_zero]
  abel

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_SUAdelic {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g : HA (AF F) σ J} :
    g ∈ SUAdelic σ J ↔ ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).det = 1 :=
  Iff.trans (show _ ↔ Matrix.GeneralLinearGroup.det (HA.mat (AF F) σ J g) = 1 from Iff.rfl) Units.ext_iff

theorem evalV_single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_single_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

theorem exists_isPlacesIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ ε, IsPlacesIdem S₁ S₂ ε := by
  classical
  refine ⟨pairA F (fun w => if w ∈ S₁ then 1 else 0) (∑ v ∈ S₂, singleV F v 1), ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact if_pos hw
  · intro w hw
    exact if_neg hw
  · intro v hv
    change evalV F v (∑ v ∈ S₂, singleV F v 1) = 1
    rw [map_sum, Finset.sum_eq_single v, evalV_single_same]
    · intro u _ hu
      exact evalV_single_ne hu.symm _
    · intro h; exact absurd hv h
  · intro v hv
    change evalV F v (∑ v ∈ S₂, singleV F v 1) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun u hu => evalV_single_ne (fun h : v = u => hv (h ▸ hu)) _

theorem not_isCompact_univ_Fv (v : HeightOneSpectrum (𝓞 F)) : ¬ IsCompact (Set.univ : Set (Fv F v)) := by
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  intro h
  obtain ⟨C, hC⟩ := (h.isBounded).exists_norm_le
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm (Fv F v) C
  exact absurd (hC x trivial) (not_le.2 hx)

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous fun a : AF F => evalV F v (sndA F a) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : AF F) :
    sigR (AF F) σ (algebraMap (AF F) (AF F ⊗[F] E) t) = algebraMap (AF F) (AF F ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem not_isCompact_split (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hM : 2 ≤ M)
    (hJ : IsHermND σ J) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : evalV F v (sndA F ε) = 1)
    (e : AF F ⊗[F] E) (he : e * e = e) (hec : e * sigR (AF F) σ e = 0)
    (hsum : e + sigR (AF F) σ e = algebraMap (AF F) (AF F ⊗[F] E) ε) : ¬ IsCompact (SUSupp σ J ε) := by
  intro hc
  set c := sigR (AF F) σ with hcdef
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have hcι : ∀ t, c (ι t) = ι t := sigR_algebraMap σ
  have hcc : c (c e) = e := by
    have h := congrArg c hsum
    rw [map_add, hcι, ← hsum, add_comm] at h
    exact add_right_cancel h
  have hce : c e * c e = c e := by rw [← map_mul, he]
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin M, i ≠ j := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hJ' : Formalism.UG.cT c (JR (F := F) (AF F) J) = JR (F := F) (AF F) J := by
    exact Matrix.ext fun a b => map_mem_HermR (AF F) σ J hJ.1 a b
  have hu : IsUnit (JR (F := F) (AF F) J).det := by
    unfold JR
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hKJ := Matrix.nonsing_inv_mul _ hu
  have hJK := Matrix.mul_nonsing_inv _ hu
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hφ1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  let lam : AF F ⊗[F] E →ₗ[AF F] AF F :=
    (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ φ.baseChange (AF F)
  have hlam : ∀ t, lam (ι t) = t := by
    intro t
    simp [lam, hι, Algebra.TensorProduct.algebraMap_apply, hφ1]
  let cl : AF F ⊗[F] E →ₗ[AF F] AF F ⊗[F] E :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun t x => by
        rw [Algebra.smul_def, map_mul, hcι, RingHom.id_apply, Algebra.smul_def] }
  let L : AF F ⊗[F] E →ₗ[AF F] AF F := lam ∘ₗ (LinearMap.id + cl) ∘ₗ LinearMap.mulLeft (AF F) e
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hent : Continuous fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hf := (continuous_evalV v).comp (hL.comp hent)
  refine not_isCompact_univ_Fv v ?_
  convert hc.image hf using 1
  symm
  rw [Set.eq_univ_iff_forall]
  intro y
  set t : AF F := pairA F 0 (singleV F v y) with ht
  have hab : (e * ι t) * (c e * ι t) = 0 := by linear_combination (ι t * ι t) * hec
  have hca : c (e * ι t) = c e * ι t := by rw [map_mul, hcι]
  have hcb : c (c e * ι t) = e * ι t := by rw [map_mul, hcι, hcc]
  have hdet := det_elt hKJ hij hab
  let g : HA (AF F) σ J :=
    (⟨Matrix.GeneralLinearGroup.mk'' _ (isUnit_iff_exists_inv.2 ⟨1, (mul_one _).trans hdet⟩), unitary_elt c hJ' hKJ hJK hij hab hca hcb⟩ : HR (AF F) σ J)
  have hg : ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      elt (JR (F := F) (AF F) J) (JR (F := F) (AF F) J)⁻¹ i j (e * ι t) (c e * ι t) := rfl
  refine ⟨g, ⟨mem_SUAdelic.2 (by rw [hg, hdet]), fun p q => ?_⟩, ?_⟩
  · rw [hg, ← hι, ← hsum]
    simp only [elt, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (ι t * Matrix.single i j (1 : AF F ⊗[F] E) p q) * (he + hec) -
      (ι t * ((JR (F := F) (AF F) J)⁻¹ * Matrix.single j i (1 : AF F ⊗[F] E) * JR (F := F) (AF F) J) p q) * (hce + hec)
  · have h1 : e * (elt (JR (F := F) (AF F) J) (JR (F := F) (AF F) J)⁻¹ i j (e * ι t) (c e * ι t)) i j = e * ι t := by
      simp only [elt, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hij,
        Matrix.single_apply_same]
      linear_combination (ι t) * he -
        (ι t * ((JR (F := F) (AF F) J)⁻¹ * Matrix.single j i (1 : AF F ⊗[F] E) * JR (F := F) (AF F) J) i j) * hec
    have h2 : L ((elt (JR (F := F) (AF F) J) (JR (F := F) (AF F) J)⁻¹ i j (e * ι t) (c e * ι t)) i j) = ε * t := by
      change lam (e * _ + c (e * _)) = _
      rw [h1, hca, ← add_mul, hsum, ← map_mul, hlam]
    change evalV F v (sndA F (L (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j))) = y
    rw [hg, h2, map_mul, map_mul, hε, one_mul]
    exact evalV_single_same v y

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem dense_split (H : StrongApproxSU) (D : D7) (V : HSp D) (hV : 2 ≤ V.rank) (e : AE D) (he : IsSplitIdem D e)
    (g : GA D V) (hg : (Formalism.L2.Theta.mt V g).det = 1) :
    g ∈ closure {x : GA D V | ∃ γ ∈ GQ V, (Formalism.L2.Theta.mt V γ).det = 1 ∧
      ∃ h : GA D V, SuppAt e V h ∧ (Formalism.L2.Theta.mt V h).det = 1 ∧ x = γ * h} := by
  obtain ⟨h1, h2, v, ε, ⟨α, hεα, hα1, hα0⟩, hsum⟩ := he
  obtain ⟨hcm, hherm⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hidem : IsPlacesIdem ∅ {v} ε := by
    subst hεα
    refine ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun w _ => rfl, fun u hu => ?_, fun u hu => ?_⟩
    · rw [Finset.mem_singleton.1 hu]; exact hα1
    · exact hα0 u (fun h => hu (Finset.mem_singleton.2 h))
  have hnc := not_isCompact_split D.sp.cm.sig hV (hherm V) v ε (hidem.2.2.1 v (Finset.mem_singleton_self v))
    e h1 h2 hsum
  refine closure_mono ?_ (H _ _ _ hcm _ _ hV (hherm V) ∅ {v} ε hidem hnc g (mem_SUAdelic.2 hg))
  rintro x ⟨γ, hγ, h, hh, rfl⟩
  refine ⟨γ, hγ.2, mem_SUAdelic.1 hγ.1, h, fun i j => ?_, mem_SUAdelic.1 hh.1, rfl⟩
  rw [hsum]
  exact hh.2 i j

end StrongApprox

end GlobalTheory.Published

end

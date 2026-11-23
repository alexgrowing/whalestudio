import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatLocal
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.StabLat

variable {F : Type} [Field F] [NumberField F]

def IntV {n : ℕ} (x : Fin n → FiniteAdeleRing (𝓞 F) F) : Prop := ∀ i, x i ∈ PIW.ClassFinD.Ohat F

def emb {n : ℕ} (y : Fin n → F) : Fin n → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F _ (y i)

theorem intV_add {n : ℕ} {x y : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) (hy : IntV y) : IntV (x + y) :=
  fun i => (PIW.ClassFinD.Ohat F).add_mem (hx i) (hy i)

theorem intV_sub {n : ℕ} {x y : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) (hy : IntV y) : IntV (x - y) :=
  fun i => (PIW.ClassFinD.Ohat F).sub_mem (hx i) (hy i)

theorem intV_smul {n : ℕ} {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ PIW.ClassFinD.Ohat F)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) : IntV (a • x) :=
  fun i => (PIW.ClassFinD.Ohat F).mul_mem ha (hx i)

theorem intV_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (hA : ∀ i j, A i j ∈ PIW.ClassFinD.Ohat F) {z : Fin n → FiniteAdeleRing (𝓞 F) F} (hz : IntV z) :
    IntV (A *ᵥ z) := fun i => by
  show ∑ j, A i j * z j ∈ _
  exact (PIW.ClassFinD.Ohat F).sum_mem fun j _ => (PIW.ClassFinD.Ohat F).mul_mem (hA i j) (hz j)

theorem intV_single {n : ℕ} (j : Fin n) : IntV (Pi.single j (1 : FiniteAdeleRing (𝓞 F) F)) := fun i => by
  by_cases h : i = j
  · subst h; rw [Pi.single_eq_same]; exact (PIW.ClassFinD.Ohat F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (PIW.ClassFinD.Ohat F).zero_mem

theorem int_mem (c : 𝓞 F) : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) ∈ PIW.ClassFinD.Ohat F :=
  fun v => by
    show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.MainNotions.BridgeLevelGenB.val_int]
    exact HeightOneSpectrum.intValuation_le_one v c

theorem exists_int_of_mem (f : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ PIW.ClassFinD.Ohat F) :
    f ∈ (algebraMap (𝓞 F) F).range :=
  HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F f fun v => by
    have hv : algebraMap F (v.adicCompletion F) f ∈ v.adicCompletionIntegers F := h v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, PI.WAU.val_algebraMap_F] at hv

theorem exists_den (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ N : ℕ, 0 < N ∧ (N : FiniteAdeleRing (𝓞 F) F) * a ∈ PIW.ClassFinD.Ohat F :=
  PI.WAU.B.exists_nat_adele a

theorem exists_den_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, (N : FiniteAdeleRing (𝓞 F) F) * A i j ∈ PIW.ClassFinD.Ohat F := by
  classical
  choose m hm h using fun q : Fin n × Fin n => exists_den (A q.1 q.2)
  refine ⟨∏ q, m q, Finset.prod_pos fun q _ => hm q, fun i j => ?_⟩
  obtain ⟨k, hk⟩ : m (i, j) ∣ ∏ q, m q := Finset.dvd_prod_of_mem m (Finset.mem_univ _)
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : FiniteAdeleRing (𝓞 F) F), mul_assoc]
  exact (PIW.ClassFinD.Ohat F).mul_mem (natCast_mem (PIW.ClassFinD.Ohat F) k) (h (i, j))

theorem exists_approx (a : FiniteAdeleRing (𝓞 F) F) (M : ℕ) (hM : 0 < M) :
    ∃ f : F, ∃ c ∈ PIW.ClassFinD.Ohat F, a = algebraMap F _ f + (M : FiniteAdeleRing (𝓞 F) F) * c := by
  obtain ⟨N, hN, hNa⟩ := exists_den a
  obtain ⟨s, c, hc, hs⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod (N * M) (Nat.mul_pos hN hM) _ (fun v => hNa v)
  refine ⟨algebraMap (𝓞 F) F s * (N : F)⁻¹, c, fun v => hc v, ?_⟩
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hinv : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹) * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, inv_mul_cancel₀ hN0, map_one]
  calc a = algebraMap F _ ((N : F)⁻¹) * ((N : FiniteAdeleRing (𝓞 F) F) * a) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
      rw [hs, map_mul, Nat.cast_mul]
      linear_combination ((M : FiniteAdeleRing (𝓞 F) F) * c) * hinv

theorem exists_approx_vec {n : ℕ} (x : Fin n → FiniteAdeleRing (𝓞 F) F) (M : ℕ) (hM : 0 < M) :
    ∃ f : Fin n → F, ∃ c : Fin n → FiniteAdeleRing (𝓞 F) F, IntV c ∧
      x = emb f + (M : FiniteAdeleRing (𝓞 F) F) • c := by
  choose f c hc h using fun i => exists_approx (x i) M hM
  exact ⟨f, c, hc, funext fun i => by simpa [emb, smul_eq_mul] using h i⟩

theorem emb_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (y : Fin n → F) :
    (A.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ emb y = emb (A *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (FiniteAdeleRing (𝓞 F) F)) A y i).symm

variable (F) in

def lat {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Submodule (𝓞 F) (Fin n → F) where
  carrier := {y | IntV (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ emb y)}
  add_mem' := by
    intro x y hx hy
    have e : emb (x + y) = emb x + (emb y : Fin n → FiniteAdeleRing (𝓞 F) F) := by
      ext i; simp [emb]
    show IntV _
    rw [e, mulVec_add]
    exact intV_add hx hy
  zero_mem' := by
    show IntV _
    have e : emb (0 : Fin n → F) = (0 : Fin n → FiniteAdeleRing (𝓞 F) F) := by ext i; simp [emb]
    rw [e, mulVec_zero]
    exact fun i => (PIW.ClassFinD.Ohat F).zero_mem
  smul_mem' := by
    intro c y hy
    have e : emb (c • y) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) • emb y := by
      ext i; simp [emb, Algebra.smul_def]
    show IntV _
    rw [e, mulVec_smul]
    exact intV_smul (int_mem c) hy

theorem mem_lat {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) (y : Fin n → F) :
    y ∈ lat F s ↔ IntV (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ emb y) := Iff.rfl

end GlobalTheory.StabLat

namespace GlobalTheory.StabLat

variable {F : Type} [Field F] [NumberField F]

theorem lat_fg {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : (lat F s).FG := by
  obtain ⟨D, hD, hDS⟩ := exists_den_mat ((s : GL (Fin n) _) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
  have hD0 : ((D : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hD.ne'
  refine Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hD0 fun y hy => ?_
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.mem_bnd]
  intro a
  apply exists_int_of_mem
  have hI : IntV ((D : FiniteAdeleRing (𝓞 F) F) • emb y) := by
    have e : (D : FiniteAdeleRing (𝓞 F) F) • emb y =
        ((D : FiniteAdeleRing (𝓞 F) F) • ((s : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
          ((((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ emb y) := by
      rw [Matrix.mulVec_mulVec, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [e]
    exact intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hDS i j) hy
  have := hI a
  simpa [emb, map_natCast] using this

theorem lat_span {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Submodule.span F (lat F s : Set (Fin n → F)) = ⊤ := by
  obtain ⟨D, hD, hDS⟩ := exists_den_mat (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)))
  have hD0 : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  have hmem : ∀ j : Fin n, (D : F) • Pi.single j (1 : F) ∈ lat F s := by
    intro j
    rw [mem_lat]
    have e : emb ((D : F) • Pi.single j (1 : F)) =
        (D : FiniteAdeleRing (𝓞 F) F) • (Pi.single j 1 : Fin n → FiniteAdeleRing (𝓞 F) F) := by
      funext i
      by_cases h : i = j
      · subst h; simp [emb]
      · simp [emb, Pi.single_eq_of_ne h]
    rw [e, Matrix.mulVec_smul]
    intro i
    rw [Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul]
    exact hDS i j
  rw [eq_top_iff, ← (Pi.basisFun F (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  have h1 : Pi.single j (1 : F) = (D : F)⁻¹ • ((D : F) • Pi.single j (1 : F)) := by
    rw [smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

theorem lat_isLattice {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Submodule.IsLattice F (lat F s) :=
  ⟨lat_fg s, lat_span s⟩

theorem matInt_conj {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) F)
    (h : ∀ y ∈ lat F s, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ lat F s) :
    PIW.ClassFinD.MatInt ((s⁻¹ * PIW.ClassFinD.glIncl F n γ * s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) := by
  set S : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) := s.val with hS
  set Si : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) := (s⁻¹).val with hSi
  set G : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) with hG
  have hA : ((s⁻¹ * PIW.ClassFinD.glIncl F n γ * s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = Si * G * S := by
    rw [Units.val_mul, Units.val_mul]; rfl
  have hSiS : Si * S = 1 := by rw [hSi, hS, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSSi : S * Si = 1 := by rw [hSi, hS, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hA]
  obtain ⟨N, hN, hNA⟩ := exists_den_mat (Si * G * S)
  obtain ⟨D, hD, hDSi⟩ := exists_den_mat Si
  suffices key : ∀ z, IntV z → IntV ((Si * G * S) *ᵥ z) by
    intro i j
    have := key (Pi.single j (1 : FiniteAdeleRing (𝓞 F) F)) (intV_single j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  intro z hz
  obtain ⟨f, c, hc, hSz⟩ := exists_approx_vec (S *ᵥ z) (N * D) (Nat.mul_pos hN hD)
  set u : Fin n → FiniteAdeleRing (𝓞 F) F := (D : FiniteAdeleRing (𝓞 F) F) • (Si *ᵥ c) with hu
  have hui : IntV u := by
    rw [hu, ← Matrix.smul_mulVec]
    exact intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hDSi i j) hc
  have hz' : Si *ᵥ emb f = z - (N : FiniteAdeleRing (𝓞 F) F) • u := by
    have e : emb f = S *ᵥ z - ((N * D : ℕ) : FiniteAdeleRing (𝓞 F) F) • c := eq_sub_of_add_eq hSz.symm
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hSiS, Matrix.one_mulVec, Matrix.mulVec_smul, hu,
      Nat.cast_mul, mul_smul]
  have hf : f ∈ lat F s := by
    rw [mem_lat]
    change IntV (Si *ᵥ emb f)
    rw [hz']
    exact intV_sub hz (intV_smul (natCast_mem _ N) hui)
  have hγf := h f hf
  rw [mem_lat, ← emb_mulVec, Matrix.mulVec_mulVec] at hγf
  have hzE : z = Si *ᵥ emb f + (N : FiniteAdeleRing (𝓞 F) F) • u := by rw [hz', sub_add_cancel]
  have e2 : (Si * G * S) *ᵥ z = (Si * G) *ᵥ emb f + ((N : FiniteAdeleRing (𝓞 F) F) • (Si * G * S)) *ᵥ u := by
    rw [hzE, Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_assoc (Si * G), hSSi, mul_one, Matrix.mulVec_smul,
      Matrix.smul_mulVec]
  rw [e2]
  exact intV_add hγf (intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNA i j) hui)

end GlobalTheory.StabLat

open GlobalTheory.StabLat in

theorem GlobalTheory.StabLat.exists_lattice_stab_conj :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
      ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsLattice F Λ ∧ ∀ γ : GL (Fin n) F,
        (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) →
          s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  intro F _ _ n s
  refine ⟨lat F s, lat_isLattice s, fun γ hγ => ⟨matInt_conj s γ fun y hy => (hγ y).2 hy, ?_⟩⟩
  have hinv : (s⁻¹ * PIW.ClassFinD.glIncl F n γ * s)⁻¹ = s⁻¹ * PIW.ClassFinD.glIncl F n γ⁻¹ * s := by
    rw [map_inv]; group
  rw [hinv]
  refine matInt_conj s γ⁻¹ fun y hy => ?_
  rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy

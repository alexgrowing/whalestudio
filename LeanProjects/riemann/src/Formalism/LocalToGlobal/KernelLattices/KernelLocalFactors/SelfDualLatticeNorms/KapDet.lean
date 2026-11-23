import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexNeZeroOfNsmulMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions
open Formalism.L2.Th1.H (stdLat pow4 imgLat relIdx IsIsom IsSelfDual dualLat altE)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

section Gen

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def Good (p : ℕ) (Lt : AddSubgroup V) (T : V →ₗ[ℂ] V) (x : V) : Prop := ∃ k : ℕ, ¬ p ∣ k ∧ (k : ℂ) • T x ∈ Lt

theorem mul_smul_mem (Lt : AddSubgroup V) {k : ℕ} {v : V} (h : (k : ℂ) • v ∈ Lt) (r : ℕ) : ((r * k : ℕ) : ℂ) • v ∈ Lt := by
  have e : ((r * k : ℕ) : ℂ) • v = r • ((k : ℂ) • v) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ r, smul_smul, Nat.cast_mul]
  rw [e]
  exact Lt.nsmul_mem h r

theorem good_zero {p : ℕ} (hp : p.Prime) (Lt : AddSubgroup V) (T : V →ₗ[ℂ] V) : Good p Lt T 0 :=
  ⟨1, hp.one_lt.ne' ∘ Nat.dvd_one.1, by rw [map_zero, smul_zero]; exact Lt.zero_mem⟩

theorem good_add {p : ℕ} (hp : p.Prime) (Lt : AddSubgroup V) (T : V →ₗ[ℂ] V) {x y : V} (hx : Good p Lt T x) (hy : Good p Lt T y) :
    Good p Lt T (x + y) := by
  obtain ⟨k, hk, h1⟩ := hx
  obtain ⟨l, hl, h2⟩ := hy
  refine ⟨l * k, fun h => (hp.dvd_mul.1 h).elim hl hk, ?_⟩
  rw [map_add, smul_add]
  refine Lt.add_mem (mul_smul_mem Lt h1 l) ?_
  rw [mul_comm]
  exact mul_smul_mem Lt h2 k

theorem good_neg {p : ℕ} (Lt : AddSubgroup V) (T : V →ₗ[ℂ] V) {x : V} (hx : Good p Lt T x) : Good p Lt T (-x) := by
  obtain ⟨k, hk, h1⟩ := hx
  refine ⟨k, hk, ?_⟩
  rw [map_neg, smul_neg]
  exact Lt.neg_mem h1

theorem good_unif {p : ℕ} (hp : p.Prime) (Lt : AddSubgroup V) [hfin : Module.Finite ℤ Lt] (T : V →ₗ[ℂ] V)
    (hT : ∀ x ∈ Lt, Good p Lt T x) : ∃ k : ℕ, ¬ p ∣ k ∧ ∀ x ∈ Lt, (k : ℂ) • T x ∈ Lt := by
  obtain ⟨S, hS⟩ := hfin.fg_top
  have hT' : ∀ x : Lt, ∃ k : ℕ, ¬ p ∣ k ∧ (k : ℂ) • T (x : V) ∈ Lt := fun x => hT x x.2
  choose kf hk1 hk2 using hT'
  refine ⟨∏ s ∈ S, kf s, ?_, ?_⟩
  · intro h
    obtain ⟨a, _, ha⟩ := (hp.prime.dvd_finsetProd_iff _).1 h
    exact hk1 a ha
  · intro x hx
    have hmem : (⟨x, hx⟩ : Lt) ∈ Submodule.span ℤ (S : Set Lt) := by rw [hS]; trivial
    have key : ∀ y : Lt, y ∈ Submodule.span ℤ (S : Set Lt) → ((∏ s ∈ S, kf s : ℕ) : ℂ) • T (y : V) ∈ Lt := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem kf hy
        rw [hr, mul_comm]
        exact mul_smul_mem Lt (hk2 y) r
      | zero => simp only [ZeroMemClass.coe_zero, map_zero, smul_zero]; exact Lt.zero_mem
      | add y z _ _ h1 h2 =>
        simp only [AddSubgroup.coe_add, map_add, smul_add]
        exact Lt.add_mem h1 h2
      | smul n y _ h1 =>
        have e : ((n • y : Lt) : V) = n • (y : V) := rfl
        rw [e, map_zsmul, smul_comm]
        exact Lt.zsmul_mem h1 n
    exact key _ hmem

end Gen

section Det

variable {m : Type} [Fintype m] [DecidableEq m]

theorem mem_std (L : PeriodPair) (x : m → ℂ) : x ∈ stdLat L m ↔ ∀ i, x i ∈ L.lattice := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem int_of_stab (L : PeriodPair) (c : ℂ) (h : ∀ ω ∈ L.lattice, c * ω ∈ L.lattice) : IsIntegral ℤ c := by
  refine isIntegral_of_smul_mem_submodule L.lattice ?_ (Module.Finite.iff_fg.1 inferInstance) c h
  intro h0
  have h1 : L.ω₁ ∈ L.lattice := L.ω₁_mem_lattice
  rw [h0, Submodule.mem_bot] at h1
  have h2 := L.indep.ne_zero 0
  exact h2 (by simpa using h1)

theorem int_det {p : ℕ} (hp : p.Prime) (L : PeriodPair) (T : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (hT : ∀ x ∈ stdLat L m, Good p (stdLat L m) T x) : ∃ k : ℕ, ¬ p ∣ k ∧ IsIntegral ℤ ((k : ℂ) * LinearMap.det T) := by
  have : Module.Finite ℤ (stdLat L m) := Formalism.L2.Th1.H.stdLat_finite L m
  obtain ⟨k, hk, hkT⟩ := good_unif hp (stdLat L m) T hT
  have hA : ∀ i j, LinearMap.toMatrix' T i j = T (Pi.single j 1) i := by
    intro i j
    rw [LinearMap.toMatrix'_apply]
  have hent : ∀ i j, IsIntegral ℤ (((k : ℂ) • LinearMap.toMatrix' T) i j) := by
    intro i j
    apply int_of_stab L
    intro ω hω
    have h1 : (Pi.single j ω : m → ℂ) ∈ stdLat L m := by
      rw [mem_std]
      intro i'
      by_cases h : i' = j
      · subst h; simpa using hω
      · rw [Pi.single_eq_of_ne h]; exact L.lattice.zero_mem
    have h2 := (mem_std L _).1 (hkT _ h1) i
    have e : (Pi.single j ω : m → ℂ) = ω • (Pi.single j 1 : m → ℂ) := by
      funext i'
      by_cases h : i' = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [e, map_smul] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [Matrix.smul_apply, hA, smul_eq_mul]
    convert h2 using 1
    ring
  refine ⟨k ^ Fintype.card m, fun h => hk (hp.dvd_of_dvd_pow h), ?_⟩
  have h3 := IsIntegral.det hent
  rw [Matrix.det_smul, LinearMap.det_toMatrix'] at h3
  rw [Nat.cast_pow]
  exact h3

end Det

section Ext

variable (D : D7)

abbrev Ix : Type := Fin 4 × D.what₂.Tau

def fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

theorem fK_apply (x : D.host.K) : fK D x = D.host.φ₀ (x : D.host.E) := rfl

def vec (v : Ix D → D.host.K) : Ix D → ℂ := fun w => fK D (v w)

def extC (f : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (fK D))

theorem extC_vec (f : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) (v : Ix D → D.host.K) :
    extC D f (vec D v) = vec D (f v) := by
  funext i
  have h := RingHom.map_mulVec (fK D) (LinearMap.toMatrix' f) v i
  rw [LinearMap.toMatrix'_mulVec] at h
  exact h.symm

theorem det_extC (f : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) :
    LinearMap.det (extC D f) = fK D (LinearMap.det f) := by
  unfold extC
  rw [LinearMap.det_toLin', ← LinearMap.det_toMatrix' f, RingHom.map_det]
  rfl

theorem vec_natsmul (s : ℕ) (v : Ix D → D.host.K) : vec D (s • v) = (s : ℂ) • vec D v := by
  funext w
  simp [vec]

theorem single_eq (j : Ix D) (ω : ℂ) : (Pi.single j ω : Ix D → ℂ) = ω • vec D (Pi.single j 1) := by
  funext i
  by_cases h : i = j
  · subst h; simp [vec]
  · simp [vec, Pi.single_eq_of_ne h]

end Ext

section Cmp

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem gaussCoord_embedding_fourfold (y : Fin 4 → D.host.E) : B.gC (emb4 D y) = vec D (B.γ₀.g y) := B.gC_spec y

theorem good_stdLat_comp_extC (p : ℕ) [hp : Fact p.Prime] (γ : IsoK D) (hγ : γ.AtP p)
    (u : (Ix D → ℂ) ≃ₗ[ℂ] (Ix D → ℂ))
    (h2 : ¬ p ∣ relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA)) :
    ∀ x ∈ stdLat B.L (Ix D), Good p (stdLat B.L (Ix D))
      ((u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) ∘ₗ extC D ((B.γ₀.g.symm.trans γ.g).symm : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K))) x := by
  intro x hx
  rw [← Finset.univ_sum_single x]
  refine Finset.sum_induction _ _ (fun a b => good_add hp.out _ _) (good_zero hp.out _ _) ?_
  intro j _
  have hω : x j ∈ TaylorLogMetric.lamOf D cc δ := (SO.mem_iff B _).1 ((mem_std B.L x).1 hx j)
  obtain ⟨s, hs, hmem⟩ := hγ.2 (Pi.single j 1) (by
    intro w
    by_cases h : w = j
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩)
  set y : Fin 4 → D.host.E := fun a => (s : D.host.E) * γ.g.symm (Pi.single j 1) a with hy
  have hy' : y = s • γ.g.symm (Pi.single j 1) := by
    funext a
    rw [hy, Pi.smul_apply, nsmul_eq_mul]
  have e1 : (s : ℂ) • extC D ((B.γ₀.g.symm.trans γ.g).symm : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) (Pi.single j (x j))
      = B.gC (x j • emb4 D y) := by
    rw [single_eq, map_smul, map_smul, extC_vec, gaussCoord_embedding_fourfold, hy', map_nsmul, vec_natsmul, smul_comm]
    rfl
  have hz : B.gC (x j • emb4 D y) ∈ B.latA := ⟨x j • emb4 D y, SO.gen_mem hω hmem, rfl⟩
  have hz2 : u (B.gC (x j • emb4 D y)) ∈ imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA := ⟨_, hz, rfl⟩
  have hz3 := PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem (stdLat B.L (Ix D)) _ hz2
  refine ⟨relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA) * s, ?_, ?_⟩
  · intro h
    rcases hp.out.dvd_mul.1 h with h | h
    · exact h2 h
    · exact hp.out.one_lt.ne' (Nat.dvd_one.1 (hs ▸ Nat.dvd_gcd h dvd_rfl))
  · rw [← e1, map_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul] at hz3
    rw [Nat.cast_mul]
    exact hz3

theorem good_lat (p : ℕ) [hp : Fact p.Prime] (γ : IsoK D) (hγ : γ.AtP p) :
    ∀ z ∈ pow4 B.lamM, Good p (stdLat B.L (Ix D))
      (extC D ((B.γ₀.g.symm.trans γ.g) : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) ∘ₗ (B.gC : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ))) z := by
  intro z hz
  have hz' := SO.fourth_power_le_closure_embeddings (TaylorLogMetric.lamOf D cc δ) hz
  clear hz
  induction hz' using AddSubgroup.closure_induction with
  | mem z h =>
    obtain ⟨w, hw, y, hy, rfl⟩ := h
    obtain ⟨s, hs, hr⟩ := hγ.1 y hy
    refine ⟨s, fun h => hp.out.one_lt.ne' (Nat.dvd_one.1 (hs ▸ Nat.dvd_gcd h dvd_rfl)), ?_⟩
    have e : (extC D ((B.γ₀.g.symm.trans γ.g) : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) ∘ₗ (B.gC : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ))) (w • emb4 D y)
        = w • vec D (γ.g y) := by
      show extC D _ (B.gC (w • emb4 D y)) = _
      rw [map_smul, map_smul, gaussCoord_embedding_fourfold, extC_vec]
      congr 2
      simp
    rw [e, mem_std]
    intro i
    obtain ⟨o, ho⟩ := hr i
    have h1 := SO.lam_mul o hw
    rw [SO.mem_iff]
    have e2 : D.host.φ₀ (((o : D.host.K) : D.host.E)) = (s : ℂ) * fK D (γ.g y i) := by
      have : fK D (algebraMap (𝓞 D.host.K) D.host.K o) = fK D ((s : D.host.K) * γ.g y i) := by rw [ho]
      rw [map_mul, map_natCast] at this
      exact this
    rw [e2] at h1
    simp only [Pi.smul_apply, smul_eq_mul, vec]
    convert h1 using 1
    ring
  | zero => exact good_zero hp.out _ _
  | add a b _ _ h1 h2 => exact good_add hp.out _ _ h1 h2
  | neg a _ h1 => exact good_neg _ _ h1

theorem relIdx_smul_mem_imgLat_of_mem_stdLat (hsd : IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Ix D)) B.latA)
    (u : (Ix D → ℂ) ≃ₗ[ℂ] (Ix D → ℂ))
    (hiso : IsIsom (Formalism.L2.Th1.H.stdH B.L (Ix D)) (Formalism.L2.Th1.H.stdH B.L (Ix D)) (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ))) :
    ∀ x ∈ stdLat B.L (Ix D),
      ((relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA) : ℕ) : ℂ) • x
        ∈ imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA := by
  intro x hx
  have hM : dualLat (Formalism.L2.Th1.H.stdH B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA)
      = imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA := SO.selfDual_img _ _ u hiso _ hsd
  have hL : dualLat (Formalism.L2.Th1.H.stdH B.L (Ix D)) (stdLat B.L (Ix D)) = stdLat B.L (Ix D) :=
    Formalism.L2.Th1.H.stdSelfDual B.L (Ix D)
  have hx' : x ∈ dualLat (Formalism.L2.Th1.H.stdH B.L (Ix D)) (stdLat B.L (Ix D)) := by rw [hL]; exact hx
  have key : ((relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA) : ℕ) : ℂ) • x
      ∈ dualLat (Formalism.L2.Th1.H.stdH B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA) := by
    intro y hy
    have h1 := PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem (stdLat B.L (Ix D)) _ hy
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
    obtain ⟨n, hn⟩ := hx' _ h1
    refine ⟨n, ?_⟩
    rw [← hn]
    simp [altE, relIdx, LinearMap.map_smulₛₗ]
  rwa [hM] at key

theorem good_alt_ter (hsd : IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Ix D)) B.latA) (p : ℕ) [hp : Fact p.Prime] (γ : IsoK D) (hγ : γ.AtP p)
    (u : (Ix D → ℂ) ≃ₗ[ℂ] (Ix D → ℂ))
    (hiso : IsIsom (Formalism.L2.Th1.H.stdH B.L (Ix D)) (Formalism.L2.Th1.H.stdH B.L (Ix D)) (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)))
    (h2 : ¬ p ∣ relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA)) :
    ∀ x ∈ stdLat B.L (Ix D), Good p (stdLat B.L (Ix D))
      (extC D ((B.γ₀.g.symm.trans γ.g) : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) ∘ₗ (u.symm : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ))) x := by
  intro x hx
  obtain ⟨z, ⟨z', hz', hzz⟩, hzx⟩ := relIdx_smul_mem_imgLat_of_mem_stdLat B hsd u hiso x hx
  obtain ⟨s, hs, hmem⟩ := good_lat B p γ hγ z' hz'
  have e1 : B.gC z' = z := hzz
  have e2 : u z = ((relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA) : ℕ) : ℂ) • x := hzx
  have e3 : z = ((relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA) : ℕ) : ℂ) • u.symm x := by
    rw [← map_smul, ← e2, LinearEquiv.symm_apply_apply]
  refine ⟨s * relIdx (stdLat B.L (Ix D)) (imgLat (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) B.latA),
    fun h => (hp.out.dvd_mul.1 h).elim hs h2, ?_⟩
  have e4 : (extC D ((B.γ₀.g.symm.trans γ.g) : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) ∘ₗ (B.gC : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ))) z'
      = extC D ((B.γ₀.g.symm.trans γ.g) : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K)) z := by
    rw [← e1]; rfl
  rw [e4, e3, map_smul, smul_smul, ← Nat.cast_mul] at hmem
  exact hmem

theorem det_compare (hsd : IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) B.latA) (p : ℕ) [hp : Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (γ : IsoK D) (hγ : γ.AtP p)
    (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hiso : IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))
      (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (h2 : ¬ p ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA)) :
    ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖
      = ‖ι (D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E))‖ := by
  obtain ⟨k₁, hk₁, hi₁⟩ := int_det hp.out B.L _ (good_stdLat_comp_extC B p γ hγ u h2)
  obtain ⟨k₂, hk₂, hi₂⟩ := int_det hp.out B.L _ (good_alt_ter B hsd p γ hγ u hiso h2)
  rw [LinearMap.det_comp, det_extC] at hi₁ hi₂
  set f := B.γ₀.g.symm.trans γ.g with hf
  set X := fK D (LinearMap.det (f : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K))) with hX
  set X' := fK D (LinearMap.det (f.symm : (Ix D → D.host.K) →ₗ[D.host.K] (Ix D → D.host.K))) with hX'
  set U := LinearMap.det (u : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) with hU
  set U' := LinearMap.det (u.symm : (Ix D → ℂ) →ₗ[ℂ] (Ix D → ℂ)) with hU'
  have hXX : X * X' = 1 := by rw [hX, hX', ← map_mul, LinearEquiv.det_mul_det_symm, map_one]
  have hUU : U * U' = 1 := LinearEquiv.det_mul_det_symm u
  have hinv : (U * X')⁻¹ = X * U' := by
    apply inv_eq_of_mul_eq_one_right
    calc U * X' * (X * U') = (U * U') * (X * X') := by ring
      _ = 1 := by rw [hXX, hUU, one_mul]
  have hne : U * X' ≠ 0 := by
    intro h0
    have : U * X' * (X * U') = 1 := by
      calc U * X' * (X * U') = (U * U') * (X * X') := by ring
        _ = 1 := by rw [hXX, hUU, one_mul]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hunit : PI.UnitaryGroupMassFormula.UnitDetRoot.IsLUnit p (U * X') := by
    refine ⟨hne, k₁ * k₂, fun h => (hp.out.dvd_mul.1 h).elim hk₁ hk₂, ?_, ?_⟩
    · have : ((k₁ * k₂ : ℕ) : ℂ) * (U * X') = (k₂ : ℂ) * ((k₁ : ℂ) * (U * X')) := by push_cast; ring
      rw [this]
      exact (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k₂ : ℤ))).mul hi₁ |> fun h => by simpa using h
    · rw [hinv]
      have : ((k₁ * k₂ : ℕ) : ℂ) * (X * U') = (k₁ : ℂ) * ((k₂ : ℂ) * (X * U')) := by push_cast; ring
      rw [this]
      exact (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k₁ : ℤ))).mul hi₂ |> fun h => by simpa using h
  have h1 := PI.UnitaryGroupMassFormula.UnitDetRoot.normOne p ι _ hunit
  rw [map_mul, norm_mul] at h1
  have h3 : ‖ι X‖ * ‖ι X'‖ = 1 := by rw [← norm_mul, ← map_mul, hXX, map_one, norm_one]
  have h4 : ‖ι X'‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  have h5 : ‖ι U‖ = ‖ι X‖ := mul_right_cancel₀ h4 (h1.trans h3.symm)
  exact h5

end Cmp

end Formalism.L2.Ker.KS

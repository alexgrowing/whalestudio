import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F

namespace SetupAlgPf

section Gen

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ}

def evB (s : ι) : Prod' H d →⋆ₐ[ℂ] (H s →L[ℂ] H s) where
  toFun a := a.1 s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def evU : Prod' H d →⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def eigSub (v : EuclideanSpace ℂ (Fin d)) : StarSubalgebra ℂ (Prod' H d) where
  carrier := {a | ∃ c : ℂ, a.2 v = c • v ∧ (star a.2) v = starRingEnd ℂ c • v}
  mul_mem' := by
    rintro a b ⟨ca, ha1, ha2⟩ ⟨cb, hb1, hb2⟩
    refine ⟨ca * cb, ?_, ?_⟩
    · simp only [Prod.snd_mul, ContinuousLinearMap.mul_apply, hb1, map_smul, ha1, smul_smul, mul_comm]
    · simp only [Prod.snd_mul, star_mul, ContinuousLinearMap.mul_apply, ha2, map_smul, hb2, smul_smul, map_mul]
  add_mem' := by
    rintro a b ⟨ca, ha1, ha2⟩ ⟨cb, hb1, hb2⟩
    refine ⟨ca + cb, ?_, ?_⟩
    · simp only [Prod.snd_add, ContinuousLinearMap.add_apply, ha1, hb1, add_smul]
    · simp only [Prod.snd_add, star_add, ContinuousLinearMap.add_apply, ha2, hb2, map_add, add_smul]
  algebraMap_mem' r := by
    refine ⟨r, ?_, ?_⟩
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp [Algebra.algebraMap_eq_smul_one, star_smul]
  star_mem' := by
    rintro a ⟨c, h1, h2⟩
    refine ⟨starRingEnd ℂ c, ?_, ?_⟩
    · simpa [Prod.snd_star] using h2
    · simpa [Prod.snd_star] using h1

def pFun (v : EuclideanSpace ℂ (Fin d)) (a : Prod' H d) : ℂ := inner ℂ v (a.2 v) / inner ℂ v v

theorem pFun_eq {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0) {a : Prod' H d} {c : ℂ} (h : a.2 v = c • v) :
    pFun v a = c := by
  rw [pFun, h, inner_smul_right, mul_div_assoc, div_self (inner_self_ne_zero.2 hv), mul_one]

theorem commute_of_adjoin {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Ring B]
    [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (f : A →⋆ₐ[ℂ] B) (b : B) (t : Set A)
    (h : ∀ x ∈ t, Commute b (f x) ∧ Commute b (star (f x))) :
    ∀ x ∈ StarAlgebra.adjoin ℂ t, Commute b (f x) := by
  intro x hx
  have hle : StarAlgebra.adjoin ℂ t ≤ (StarSubalgebra.centralizer ℂ ({b} : Set B)).comap f := by
    apply StarAlgebra.adjoin_le
    intro y hy
    show f y ∈ StarSubalgebra.centralizer ℂ ({b} : Set B)
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro g rfl
    refine ⟨(h y hy).1.eq, ?_⟩
    have := congrArg star (h y hy).2.eq
    simp only [star_mul, star_star] at this
    exact this.symm
  have hm : f x ∈ StarSubalgebra.centralizer ℂ ({b} : Set B) := hle hx
  rw [StarSubalgebra.mem_centralizer_iff] at hm
  exact (hm b rfl).1

end Gen

theorem coe_pow_clm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : V →L[ℂ] V) (k : ℕ) :
    ((f ^ k : V →L[ℂ] V) : V →ₗ[ℂ] V) = (f : V →ₗ[ℂ] V) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ContinuousLinearMap.toLinearMap_mul, ih]

section Build

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

abbrev Alg (gen : Γ → Prod' H d) : Type := StarAlgebra.adjoin ℂ (Set.range gen)

abbrev algCR (gen : Γ → Prod' H d) (h1 : ∀ x y, Commute (gen x) (gen y))
    (h2 : ∀ x y, Commute (gen x) (star (gen y))) : CommRing (Alg gen) :=
  { (inferInstance : Ring (Alg gen)) with
    mul_comm := by
      haveI := StarAlgebra.isMulCommutative_adjoin ℂ (s := Set.range gen)
        (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact (h1 x y).eq) (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact (h2 x y).eq)
      exact mul_comm' }

def Rb (gen : Γ → Prod' H d) (s : ι) : Alg gen →⋆ₐ[ℂ] (H s →L[ℂ] H s) :=
  (evB s).comp (StarSubalgebra.subtype _)

def ρU (gen : Γ → Prod' H d) : Alg gen →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin d)) where
  toFun a := ((a : Prod' H d).2 : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    ext w
    simp [Algebra.algebraMap_eq_smul_one]

theorem mem_eig (gen : Γ → Prod' H d) (v : EuclideanSpace ℂ (Fin d))
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) (a : Alg gen) :
    (a : Prod' H d) ∈ eigSub v :=
  StarAlgebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact heig x) a.2

theorem hpv (gen : Γ → Prod' H d) {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0)
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) (a : Alg gen) :
    (a : Prod' H d).2 v = pFun v (a : Prod' H d) • v := by
  obtain ⟨c, h1, _⟩ := mem_eig gen v heig a
  rw [pFun_eq hv h1, h1]

theorem hps (gen : Γ → Prod' H d) {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0)
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) (a : Alg gen) :
    (star (a : Prod' H d).2) v = starRingEnd ℂ (pFun v (a : Prod' H d)) • v := by
  obtain ⟨c, h1, h2⟩ := mem_eig gen v heig a
  rw [pFun_eq hv h1, h2]

def pU (gen : Γ → Prod' H d) {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0)
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) :
    Alg gen →⋆ₐ[ℂ] ℂ where
  toFun a := pFun v (a : Prod' H d)
  map_one' := pFun_eq hv (by simp)
  map_mul' a b := pFun_eq hv (by
    show (a : Prod' H d).2 ((b : Prod' H d).2 v) = _
    rw [hpv gen hv heig b, map_smul, hpv gen hv heig a, smul_smul, mul_comm])
  map_zero' := pFun_eq hv (by simp)
  map_add' a b := pFun_eq hv (by
    show (a : Prod' H d).2 v + (b : Prod' H d).2 v = _
    rw [hpv gen hv heig a, hpv gen hv heig b, add_smul])
  commutes' r := pFun_eq hv (by simp [Algebra.algebraMap_eq_smul_one])
  map_star' a := pFun_eq hv (by
    show (star (a : Prod' H d).2) v = _
    rw [hps gen hv heig a, starRingEnd_apply])

theorem commU_lem (gen : Γ → Prod' H d) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hu : ∀ x, Commute u (gen x).2 ∧ Commute u (star (gen x).2)) (g : Alg gen) :
    Commute (u : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (ρU gen g) := by
  have h := commute_of_adjoin (evU (H := H)) u _ (by rintro _ ⟨x, rfl⟩; exact hu x) _ g.2
  have h' := congrArg (fun f : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) =>
    (f : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))) h.eq
  simp only [ContinuousLinearMap.toLinearMap_mul] at h'
  exact h'

theorem comm_lem (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s)
    (hb : ∀ s x, Commute (β s) ((gen x).1 s) ∧ Commute (β s) (star ((gen x).1 s))) (s : ι) (g : Alg gen) :
    Commute (β s) (Rb gen s g) :=
  commute_of_adjoin (evB s) (β s) _ (by rintro _ ⟨x, rfl⟩; exact hb s x) _ g.2

end Build

end SetupAlgPf

open SetupAlgPf in
theorem setupAlg : SetupAlg := by
  intro E _ _ _ n π S T K W X
  let _ := X.ft; let _ := X.ne; let _ := X.ng; let _ := X.ip; let _ := X.cs
  have hg0 : X.gen X.a₀ ∈ StarAlgebra.adjoin ℂ (Set.range X.gen) := StarAlgebra.subset_adjoin ℂ _ ⟨X.a₀, rfl⟩
  refine ⟨{
      A := Alg X.gen
      cr := algCR X.gen X.comm X.commStar
      sr := (inferInstance : StarRing (Alg X.gen))
      al := (inferInstance : Algebra ℂ (Alg X.gen))
      sm := (inferInstance : StarModule ℂ (Alg X.gen))
      ι := X.ι
      H := X.H
      R := Rb X.gen
      β := X.β
      m := X.m
      V := EuclideanSpace ℂ (Fin X.d)
      ρ := ρU X.gen
      u := (X.u : EuclideanSpace ℂ (Fin X.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin X.d))
      p := pU X.gen X.v_ne X.eigv
      a₀ := ⟨X.gen X.a₀, hg0⟩
      pa₀ := ?_
      comm := comm_lem X.gen X.β X.βcomm
      commU := commU_lem X.gen X.u X.ucomm
      bound := ?_
      eig := ⟨X.v, X.v_ne, X.uv, fun g => hpv X.gen X.v_ne X.eigv g⟩
      read := ?_ }⟩
  · obtain ⟨c, hc, h⟩ := X.a₀v
    show pFun X.v (X.gen X.a₀) ≠ 0
    rw [pFun_eq X.v_ne h]
    exact hc
  · intro g hg
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hg
    obtain ⟨C, N, j, h⟩ := X.bound g.1 g.2 ⟨b.1, b.2, by rw [← hb]; rfl⟩
    refine ⟨C, N, j, h.mono fun k hk => ?_⟩
    have e : ((X.u : EuclideanSpace ℂ (Fin X.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin X.d)) * ρU X.gen g) ^ k =
        (((X.u * (g : Prod' X.H X.d).2) ^ k : EuclideanSpace ℂ (Fin X.d) →L[ℂ] EuclideanSpace ℂ (Fin X.d)) :
          EuclideanSpace ℂ (Fin X.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin X.d)) := by
      rw [coe_pow_clm, ContinuousLinearMap.toLinearMap_mul]
      rfl
    rw [e]
    exact hk
  · intro s χ hb hp h3
    exact X.read s χ hb (fun a _ => ⟨pU X.gen X.v_ne X.eigv a, hpv X.gen X.v_ne X.eigv a, hp a⟩) h3

end PositivityTheory.Rg.BcB.F

end

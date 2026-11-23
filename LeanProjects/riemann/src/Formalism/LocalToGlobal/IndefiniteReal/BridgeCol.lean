import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV Formalism.L2.Col

structure AdPts {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) {G Γ : Type} [Group G] [Group Γ]
    (ι : Γ →* G) (J : Subgroup G) where
  K1 : Subgroup G
  principal_congruence_le : K1 ≤ J
  q : G → S.D
  gl : Γ × J →* S.G
  gl_surj : Function.Surjective gl
  gl_ker : ∀ (γ : Γ) (k : J), gl (γ, k) = 1 ↔ γ = 1 ∧ (k : G) ∈ K1
  q_surj : Function.Surjective q
  q_eqv : ∀ (γ : Γ) (k : J) (x : G), q (ι γ * x * (k : G)⁻¹) = gl (γ, k) • q x
  q_fib : ∀ x x' : G, q x = q x' ↔ ∃ k1 ∈ K1, x' = x * k1

section Stab

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {J : Subgroup G}

def stabJ {y : G} (γ : stab ι J y) : J := ⟨y⁻¹ * ι (γ : Γ) * y, (mem_stab ι).1 γ.2⟩

theorem stabK_eq_inv {y : G} (γ : stab ι J y) : stabK ι γ = (stabJ γ)⁻¹ := rfl

def stabHom (y : G) : stab ι J y →* Γ × J where
  toFun γ := ((γ : Γ), stabJ γ)
  map_one' := Prod.ext rfl (Subtype.ext (by simp [stabJ]))
  map_mul' a b := Prod.ext rfl (Subtype.ext (by
    show y⁻¹ * ι ((a : Γ) * (b : Γ)) * y = (y⁻¹ * ι (a : Γ) * y) * (y⁻¹ * ι (b : Γ) * y)
    rw [map_mul]; group))

end Stab

namespace AdPts

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G} (A : AdPts S ι J)

theorem q_mul (γ : Γ) (x : G) (k : J) : A.q (ι γ * x * (k : G)) = A.gl (γ, k⁻¹) • A.q x := by
  have h := A.q_eqv γ k⁻¹ x
  simpa using h

def y (c : S.Cl) : G := Function.surjInv A.q_surj (S.outSec.rep c)

theorem q_y (c : S.Cl) : A.q (A.y c) = S.outSec.rep c := Function.surjInv_eq A.q_surj _

theorem isReps : IsReps ι J A.y := by
  intro h
  refine ⟨S.cls (A.q h), ?_, ?_⟩
  · obtain ⟨g, hg⟩ := S.outSec.exists_mv (A.q h)
    obtain ⟨⟨γ, k⟩, rfl⟩ := A.gl_surj g
    rw [← A.q_y, ← A.q_eqv] at hg
    obtain ⟨k1, hk1, e⟩ := (A.q_fib _ _).1 hg
    refine ⟨γ, k⁻¹ * ⟨k1, A.principal_congruence_le hk1⟩, e.trans ?_⟩
    simp [mul_assoc]
  · rintro c ⟨γ, k, rfl⟩
    rw [A.q_mul, S.cls_smul, A.q_y, S.outSec.spec]

def toStab (c : S.Cl) : stab ι J (A.y c) →* MulAction.stabilizer S.G (S.outSec.rep c) :=
  (A.gl.comp (stabHom (A.y c))).codRestrict _ (fun γ => by
    rw [MulAction.mem_stabilizer_iff]
    show A.gl ((γ : Γ), stabJ γ) • S.outSec.rep c = S.outSec.rep c
    rw [← A.q_y, ← A.q_eqv]
    congr 1
    show ι (γ : Γ) * A.y c * ((A.y c)⁻¹ * ι (γ : Γ) * A.y c)⁻¹ = A.y c
    group)

theorem toStab_coe (c : S.Cl) (γ : stab ι J (A.y c)) :
    ((A.toStab c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) = A.gl ((γ : Γ), stabJ γ) := rfl

theorem toStab_bij (c : S.Cl) : Function.Bijective (A.toStab c) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
    have h1 : A.gl ((γ : Γ), stabJ γ) = 1 := by
      rw [← A.toStab_coe, hγ]
      rfl
    exact Subtype.ext ((A.gl_ker _ _).1 h1).1
  · intro g
    obtain ⟨⟨γ, k⟩, hg⟩ := A.gl_surj g
    have hfix : A.gl (γ, k) • S.outSec.rep c = S.outSec.rep c := by
      rw [hg]
      exact g.2
    rw [← A.q_y, ← A.q_eqv] at hfix
    obtain ⟨k1, hk1, e⟩ := (A.q_fib _ _).1 hfix.symm
    have hmem : (A.y c)⁻¹ * ι γ * A.y c = k1 * (k : G) := by
      calc (A.y c)⁻¹ * ι γ * A.y c = (A.y c)⁻¹ * (ι γ * A.y c * (k : G)⁻¹) * k := by group
        _ = k1 * (k : G) := by rw [e]; group
    have hs : γ ∈ stab ι J (A.y c) := by
      rw [mem_stab, hmem]
      exact J.mul_mem (A.principal_congruence_le hk1) k.2
    refine ⟨⟨γ, hs⟩, Subtype.ext ?_⟩
    rw [toStab_coe, ← hg]
    have hJ : (stabJ (⟨γ, hs⟩ : stab ι J (A.y c)) : J) = ⟨k1, A.principal_congruence_le hk1⟩ * k := Subtype.ext hmem
    have h1 : A.gl ((1 : Γ), (⟨k1, A.principal_congruence_le hk1⟩ : J)) = 1 := (A.gl_ker _ _).2 ⟨rfl, hk1⟩
    have e2 : ((γ, stabJ (⟨γ, hs⟩ : stab ι J (A.y c))) : Γ × J) = ((1 : Γ), (⟨k1, A.principal_congruence_le hk1⟩ : J)) * (γ, k) := by
      rw [hJ]
      exact Prod.ext (one_mul γ).symm rfl
    rw [e2, map_mul, h1, one_mul]

def stabEquiv (c : S.Cl) : stab ι J (A.y c) ≃* MulAction.stabilizer S.G (S.outSec.rep c) :=
  MulEquiv.ofBijective (A.toStab c) (A.toStab_bij c)

end AdPts

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def classPresOf {S : GSD K} {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {J : Subgroup G} (A : AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (_hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres ι (S.toCSD h) σ ρ J χ where
  y := A.y
  reps := A.isReps
  stabI c := (A.stabEquiv c).symm
  coef := coef
  coef_li := hli
  coef_span := hspan
  coef_pair := hpair
  coef_act := by
    intro c g x
    obtain ⟨γ, rfl⟩ := (A.stabEquiv c).surjective g
    show coef (S.ρ ((A.stabEquiv c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) x) =
      (χ (stabK ι ((A.stabEquiv c).symm (A.stabEquiv c γ))) : ℂ) • ρ (((A.stabEquiv c).symm (A.stabEquiv c γ)) : Γ) (coef x)
    rw [MulEquiv.symm_apply_apply]
    have e1 : ((A.stabEquiv c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) = A.gl ((γ : Γ), stabJ γ) := rfl
    rw [e1, hgl, Units.smul_def, stabK_eq_inv, map_inv]

namespace ClassPres

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'}
  {χ' : J' →* ℂˣ}

theorem mem_stab_transport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) (γ : Γ) : eΓ γ ∈ stab ι' J' (eG y) ↔ γ ∈ stab ι J y := by
  rw [mem_stab, mem_stab, hJ, hι]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

def stabTransport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) : stab ι J y ≃* stab ι' J' (eG y) where
  toFun γ := ⟨eΓ γ, (mem_stab_transport eG eΓ hι hJ y γ).2 γ.2⟩
  invFun γ' := ⟨eΓ.symm γ', (mem_stab_transport eG eΓ hι hJ y _).1 (by rw [MulEquiv.apply_symm_apply]; exact γ'.2)⟩
  left_inv γ := Subtype.ext (eΓ.symm_apply_apply _)
  right_inv γ' := Subtype.ext (eΓ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul eΓ _ _)

theorem stabK_transport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) (γ : stab ι J y) :
    ((stabK ι' (stabTransport eG eΓ hι hJ y γ) : J') : G') = eG (stabK ι γ : G) := by
  show ((eG y)⁻¹ * ι' (eΓ (γ : Γ)) * eG y)⁻¹ = eG ((y⁻¹ * ι (γ : Γ) * y)⁻¹)
  rw [hι]
  simp only [map_mul, map_inv]

def transport (P : ClassPres ι S σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) : ClassPres ι' S σ ρ' J' χ' :=
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  { y := fun c => eG (P.y c)
    reps := by
      intro h'
      obtain ⟨c, ⟨γ, k, hk⟩, hu⟩ := P.reps (eG.symm h')
      refine ⟨c, ⟨eΓ γ, ⟨eG k, (hJ' _).2 (by rw [MulEquiv.symm_apply_apply]; exact k.2)⟩, ?_⟩, ?_⟩
      · show h' = ι' (eΓ γ) * eG (P.y c) * eG (k : G)
        rw [hι, ← map_mul, ← map_mul, ← hk, MulEquiv.apply_symm_apply]
      · rintro c' ⟨γ', k', hk'⟩
        refine hu c' ⟨eΓ.symm γ', ⟨eG.symm k', (hJ' _).1 k'.2⟩, ?_⟩
        rw [hk']
        have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
          rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
        rw [e]
        simp only [map_mul, MulEquiv.symm_apply_apply]
    stabI := fun c => (P.stabI c).trans (stabTransport eG eΓ hι hJ' (P.y c))
    coef := P.coef
    coef_li := P.coef_li
    coef_span := P.coef_span
    coef_pair := P.coef_pair
    coef_act := by
      intro c g x
      have hk : stabK ι' (stabTransport eG eΓ hι hJ' (P.y c) (P.stabI c g)) =
          ⟨eG (stabK ι (P.stabI c g) : G), (hJ' _).2 (by rw [MulEquiv.symm_apply_apply]; exact (stabK ι (P.stabI c g)).2)⟩ :=
        Subtype.ext (stabK_transport eG eΓ hι hJ' (P.y c) (P.stabI c g))
      show P.coef (S.ρ c g x) = (χ' (stabK ι' (stabTransport eG eΓ hι hJ' (P.y c) (P.stabI c g))) : ℂ) •
        ρ' (eΓ (P.stabI c g : Γ)) (P.coef x)
      rw [hk, hχ, hρ, P.coef_act] }

end ClassPres

end Formalism.IndefR.Bridge

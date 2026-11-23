import Formalism.SharpRestriction.GrowthBounds.ChartComparison.KerLabelsMu
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocCore
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsOrb

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PStabEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p}

def LocHypC (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) : Prop :=
  ∀ v (x : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ S.Uloc (A.pl v).1 →
    (∀ a b, (((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) ∧
    ∀ a b, ((((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F

def GamOnto (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (i : G.comp) : Prop :=
  ∀ δ : GL (Fin n) E, δ ∈ UJ (σ : E →+* E) J →
    (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
      bc (prV (E := E) w) ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * A.yG i) ∈ S.Uloc w) →
    δ ∈ (A.gamI i).range

def StabAt (S : StepLevel F E σ J T f bad) (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Type :=
  {δ : GL (Fin n) E // δ ∈ UJ (σ : E →+* E) J ∧ x⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * x ∈ S.U}

theorem int_of_eQ {A : LocAt F E n G} (hW : LocInt A) (v : Fin G.P.nV) (h : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hh : ∀ a b, (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) (a b : Fin (G.P.m + 1)) :
    (h : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) a b ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  have h1 := hh (Fin.cast A.rk a) (Fin.cast A.rk b)
  have h2 : (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _)
      (Fin.cast A.rk a) (Fin.cast A.rk b) = A.eQ v ((h : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) a b) := by
    show A.eQ v ((castGL A.rk (G.P.Qq v) h : Matrix (Fin n) (Fin n) _) (Fin.cast A.rk a) (Fin.cast A.rk b)) = _
    rw [castGL_apply]
    simp
  rw [h2] at h1
  exact (hW v _).2 h1

variable {A : LocAt F E n G} (S : StepLevel F E σ J T f bad)

theorem ff_quot (i : G.comp) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x x' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : A.IsPt i g x) (hx' : A.IsPt i g' x') (v : Fin G.P.nV) :
    (bc (A.phE v) A.B)⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (x⁻¹ * x')) * bc (A.phE v) A.B =
      bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) ((g v)⁻¹ * g' v)) := by
  rw [map_mul, map_mul, map_inv, map_inv, hx.2 v, hx'.2 v, map_mul, map_mul, map_inv, map_inv]
  group

variable {S}

theorem bc_mem {γ : GL (Fin n) E} (hγ : γ ∈ UJ (σ : E →+* E) J) :
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  Formalism.UG.P.rational_points_le_holds F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩

theorem U_le {y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hy : y ∈ S.U) : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  ((S.U_eq y).1 hy).1

section Stab

variable (H : LocGood σ J A) (hW : LocInt A) (hH : LocHyp S A) (hHc : LocHypC S A) (hbad : ∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal)
  (hA : A.ActB)
  (hΓ : ∀ i (γ : (G.lev i).Γ), (A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i ∈
        UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w)
        ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i) ∈ S.Uloc w)
  (hU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J)

theorem smul_colSpan (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) (v : Fin G.P.nV) :
    (G.lev i).smul γ L v = colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  show (L v).map _ = _
  rw [hL v, colSpan_map]
  rfl

include H hW hH hbad hA hΓ hU in

theorem fix_mem (i : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x.1) (γ : (G.lev i).Γ) (hfix : (G.lev i).smul γ L = L) :
    x.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 ∈ S.U := by
  obtain ⟨κ, hκ⟩ := awayEx_of H S hΓ i γ
  have hx' := A.isPt_smul hA i g x.1 κ.1 hx γ hκ
  have hL' : ∀ v, L v = colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro v
    rw [← smul_colSpan i γ L g hL v, hfix]
  have hm : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 * κ.1⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem (hU i γ)) x.2) (Subgroup.inv_mem _ (U_le κ.2))
  obtain ⟨κ', e, -⟩ := ptOne_of S hW hH hbad i L g _ x ⟨_, hm⟩ hL hL' hx hx'
  have e2 : x.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 = κ'.1 * κ.1 := by
    have e' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 * κ.1⁻¹ = x.1 * κ'.1 := e
    calc x.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1
        = x.1⁻¹ * (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 * κ.1⁻¹) * κ.1 := by group
      _ = κ'.1 * κ.1 := by rw [e']; group
  rw [e2]
  exact S.U.mul_mem κ'.2 κ.2

include H hW hHc hA hΓ in

theorem fix_of_mem (i : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x.1) (γ : (G.lev i).Γ)
    (hm : x.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 ∈ S.U) : (G.lev i).smul γ L = L := by
  obtain ⟨κ, hκ⟩ := awayEx_of H S hΓ i γ
  have hx' := A.isPt_smul hA i g x.1 κ.1 hx γ hκ
  have hmU : x.1⁻¹ * (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 * κ.1⁻¹) ∈ S.U := by
    have : x.1⁻¹ * (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1 * κ.1⁻¹) =
        (x.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x.1) * κ.1⁻¹ := by group
    rw [this]
    exact S.U.mul_mem hm (S.U.inv_mem κ.2)
  funext v
  have hloc := ((S.U_eq _).1 hmU).2 (A.pl v).1
  obtain ⟨h1, h2⟩ := hHc v _ hloc
  rw [ff_quot i g _ x.1 _ hx hx' v] at h1 h2
  rw [← map_inv, ← map_inv] at h2
  have hst : (g v)⁻¹ * ((G.lev i).act v γ * g v) ∈ stabStd (k := G.P.m + 1) (Qq := G.P.Qq v) (G.P.W v) :=
    (stabStd_iff _ _).2 ⟨int_of_eQ hW v _ h1, int_of_eQ hW v _ h2⟩
  rw [smul_colSpan i γ L g hL v, hL v, colSpan_eq, colSpan_eq]
  exact (gMap_std_eq_iff _ _ _).2 hst

include H hW hH hHc hbad hA hΓ hU in

theorem stab_bij (i : G.comp) (hinj : Function.Injective (A.gamI i)) (hon : GamOnto S A i) (L : G.P.Tup)
    (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x.1) :
    Function.Bijective (fun γ : {γ : (G.lev i).Γ // (G.lev i).smul γ L = L} =>
      (⟨A.gamI i γ.1, hU i γ.1, fix_mem H hW hH hbad hA hΓ hU i L g hL x hx γ.1 γ.2⟩ : StabAt S x.1)) := by
  refine ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)), fun δ => ?_⟩
  obtain ⟨δ, hδ, hδx⟩ := δ
  have hoff : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
      bc (prV (E := E) w) ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * A.yG i) ∈ S.Uloc w := by
    intro w hw
    have h1 := ((S.U_eq _).1 hδx).2 w
    rw [map_mul, map_mul, map_inv, hx.1 w hw] at h1
    rw [map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨γ, rfl⟩ := hon δ hδ hoff
  exact ⟨⟨γ, fix_of_mem H hW hHc hA hΓ i L g hL x hx γ hδx⟩, rfl⟩

theorem conj_mem (x y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ₀ d : GL (Fin n) E) (κ₀ : S.U)
    (e : x = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1)
    (hd : x⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) d * x ∈ S.U) :
    y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₀⁻¹ * d * γ₀) * y ∈ S.U := by
  subst e
  have : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₀⁻¹ * d * γ₀) * y =
      κ₀.1 * ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) d *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1)) * κ₀.1⁻¹ := by
    rw [map_mul, map_mul, map_inv]; group
  rw [this]
  exact S.U.mul_mem (S.U.mul_mem κ₀.2 hd) (S.U.inv_mem κ₀.2)

theorem conj_mem' (x y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ₀ d : GL (Fin n) E) (κ₀ : S.U)
    (e : x = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1)
    (hd : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) d * y ∈ S.U) :
    x⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₀ * d * γ₀⁻¹) * x ∈ S.U := by
  subst e
  have : (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1)⁻¹ *
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₀ * d * γ₀⁻¹) *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1) =
      κ₀.1⁻¹ * (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) d * y) * κ₀.1 := by
    rw [map_mul, map_mul, map_inv]; group
  rw [this]
  exact S.U.mul_mem (S.U.mul_mem (S.U.inv_mem κ₀.2) hd) κ₀.2

set_option maxHeartbeats 2000000 in
include H hW hH hbad in

theorem cls_unique {cl : Type} (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : Function.Injective (fun c => (Quotient.mk'' (y c) : Cls S))) (i : G.comp) (L : G.P.Tup)
    (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hL' : ∀ v, L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (c c' : cl) (γ₁ γ₂ : GL (Fin n) E) (hγ₁ : γ₁ ∈ UJ (σ : E →+* E) J) (hγ₂ : γ₂ ∈ UJ (σ : E →+* E) J) (κ₁ κ₂ : S.U)
    (h1 : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₁ * (y c).1 * κ₁.1))
    (h2 : A.IsPt i g' (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₂ * (y c').1 * κ₂.1)) : c = c' := by
  obtain ⟨κ, e, -⟩ := ptOne_of S hW hH hbad i L g g'
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₁) (y c).2) (U_le κ₁.2)⟩
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₂) (y c').2) (U_le κ₂.2)⟩ hL hL' h1 h2
  have e' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₂ * (y c').1 * κ₂.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₁ * (y c).1 * κ₁.1 * κ.1 := e
  have hγ : γ₂⁻¹ * γ₁ ∈ UJ (σ : E →+* E) J := Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ₂) hγ₁
  have hκ : κ₁.1 * κ.1 * κ₂.1⁻¹ ∈ S.U := S.U.mul_mem (S.U.mul_mem κ₁.2 κ.2) (S.U.inv_mem κ₂.2)
  apply hy
  show (Quotient.mk'' (y c) : Cls S) = Quotient.mk'' (y c')
  refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, bc_mem hγ⟩, Subgroup.mem_subgroupOf.2 ⟨γ₂⁻¹ * γ₁, hγ, rfl⟩, ⟨_, U_le hκ⟩,
    Subgroup.mem_subgroupOf.2 hκ, Subtype.ext ?_⟩
  show (y c').1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₂⁻¹ * γ₁) * (y c).1 * (κ₁.1 * κ.1 * κ₂.1⁻¹)
  have : (y c').1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₂)⁻¹ *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₂ * (y c').1 * κ₂.1) * κ₂.1⁻¹ := by group
  rw [this, e', map_mul, map_inv]
  group

def stabConj (x y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ₀ : GL (Fin n) E) (hγ₀ : γ₀ ∈ UJ (σ : E →+* E) J) (κ₀ : S.U)
    (e : x = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1) : StabAt S x ≃ StabAt S y where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ₀) δ.2.1) hγ₀,
    conj_mem x y γ₀ δ.1 κ₀ e δ.2.2⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ₀ δ.2.1) (Subgroup.inv_mem _ hγ₀),
    conj_mem' x y γ₀ δ.1 κ₀ e δ.2.2⟩
  left_inv δ := Subtype.ext (by show γ₀ * (γ₀⁻¹ * δ.1 * γ₀) * γ₀⁻¹ = δ.1; group)
  right_inv δ := Subtype.ext (by show γ₀⁻¹ * (γ₀ * δ.1 * γ₀⁻¹) * γ₀ = δ.1; group)

def stabCls {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J) (hinj : ∀ c, Function.Injective (stabI c))
    (hrange : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom) (c : cl) :
    stab c ≃ StabAt S (y c).1 :=
  Equiv.ofBijective (fun s => ⟨(stabI c s).1, (stabI c s).2,
      (mem_map_conj S.U _ _).1 ((hrange c (stabI c s)).1 ⟨s, rfl⟩)⟩)
    ⟨fun a b hab => hinj c (Subtype.ext (congrArg (fun z : StabAt S (y c).1 => z.1) hab)), fun δ => by
      obtain ⟨s, hs⟩ := (hrange c ⟨δ.1, δ.2.1⟩).2 ((mem_map_conj S.U _ _).2 δ.2.2)
      exact ⟨s, Subtype.ext (show (stabI c s).1 = δ.1 from congrArg Subtype.val hs)⟩⟩

include H hW hH hHc hbad hA hΓ hU in

theorem card_eq (i : G.comp) (hinj : Function.Injective (A.gamI i)) (hon : GamOnto S A i) (L : G.P.Tup)
    (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J) (hsinj : ∀ c, Function.Injective (stabI c))
    (hrange : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (c : cl) (γ₀ : GL (Fin n) E) (hγ₀ : γ₀ ∈ UJ (σ : E →+* E) J) (κ₀ : S.U)
    (hx : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (y c).1 * κ₀.1)) :
    Nat.card (stab c) = Nat.card {γ : (G.lev i).Γ // (G.lev i).smul γ L = L} := by
  let x : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₀) (y c).2) (U_le κ₀.2)⟩
  have e1 := Nat.card_congr (Equiv.ofBijective _ (stab_bij H hW hH hHc hbad hA hΓ hU i hinj hon L g hL x hx))
  have e2 := Nat.card_congr (stabConj x.1 (y c).1 γ₀ hγ₀ κ₀ rfl)
  have e3 := Nat.card_congr (stabCls y stabI hsinj hrange c)
  rw [e3, ← e2]
  exact e1.symm

end Stab

end Gen

section LocJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reGL_symm_mem_UJ {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (g : GL (Fin b) R)
    (hg : g ∈ UJ σ J') : (reGL h R).symm g ∈ UJ σ J := by
  subst h
  have e1 : J' = J := by ext x y; exact hJ x y
  subst e1
  have e2 : (reGL (rfl : a = a) R).symm g = g := by rw [MulEquiv.symm_apply_eq, reGL_rfl]
  rw [e2]
  exact hg

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)
  {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad)

theorem gamI_inj_locJ (c : cmp) : Function.Injective ((locJ hi t B).gamI c) := by
  intro a b hab
  apply t.gamI_inj c
  apply Subtype.ext
  exact (reGL (rankN D (i + 1) hi) D.host.E).injective hab

set_option maxHeartbeats 4000000 in

theorem gamOnto_locJ (hU : SameUlocJ hi S Uloc) (c : cmp) : GamOnto S (locJ hi t B) c := by
  intro δ hδ hoff
  have hδ0 : (reGL (rankN D (i + 1) hi) D.host.E).symm δ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram :=
    reGL_symm_mem_UJ (rankN D (i + 1) hi) _ _ _ (gramN_apply D (i + 1) hi) δ hδ
  have eδ : δ = reGL (rankN D (i + 1) hi) D.host.E ((reGL (rankN D (i + 1) hi) D.host.E).symm δ) :=
    (MulEquiv.apply_symm_apply _ _).symm
  set δ0 := (reGL (rankN D (i + 1) hi) D.host.E).symm δ with hδ0def
  have hz : ((t.yG c).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1 ∈
      awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) := by
    rw [mem_awayG]
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (t.yG c).2) (bc_mem hδ0)) (t.yG c).2, fun w' hw' => ?_⟩
    have h1 := hoff w' hw'
    have e1 : ((locJ hi t B).yG c)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (locJ hi t B).yG c =
        reGL (rankN D (i + 1) hi) _ (((t.yG c).1)⁻¹ *
          bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1) := by
      rw [eδ, map_mul, map_mul, map_inv, ← bc_reGL]
      rfl
    rw [e1, bc_reGL, hU w'] at h1
    exact (Subgroup.mem_map_iff_mem (f := (reGL (rankN D (i + 1) hi) _).toMonoidHom)
      (reGL (rankN D (i + 1) hi) _).injective).1 h1
  obtain ⟨γ, hγ⟩ := (t.gamI_range c ⟨δ0, hδ0⟩).2 ((mem_map_conj _ _ _).2 hz)
  refine ⟨γ, ?_⟩
  show reGL (rankN D (i + 1) hi) D.host.E (t.gamI c γ).1 = δ
  rw [hγ]
  exact eδ.symm

theorem locHypC_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {p : ℕ} {G : GAtP p}
    {k : ℕ} (hk : k = n) (A : LocAt F E n G) (S : StepLevel F E σ J T f bad) (B0 : GL (Fin k) E) (hB : A.B = reGL hk E B0)
    (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)))
    (hU : ∀ v, S.Uloc v = (Uloc0 v).map (reGL hk _).toMonoidHom)
    (h0 : ∀ v (x : GL (Fin k) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ Uloc0 (A.pl v).1 →
      (∀ a b, (((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) ∧
      ∀ a b, ((((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0)⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) : LocHypC S A := by
  subst hk
  have hre : ∀ (R : Type) [CommRing R] (g : GL (Fin k) R), reGL (rfl : k = k) R g = g := by
    intro R _ g; apply Units.ext; ext x y; rfl
  rw [hre] at hB
  intro v x hx
  rw [hU] at hx
  obtain ⟨x0, hx0, e⟩ := Subgroup.mem_map.1 hx
  have e' : x = x0 := by rw [← e]; exact hre _ x0
  subst e'
  rw [hB]
  exact h0 v x hx0

def HypTJC : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)), x ∈ Uloc w' →
    (∀ a b, (((t.fr w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom) x * t.fr w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((t.fr w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom) x * t.fr w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F

set_option maxHeartbeats 4000000 in

theorem locHypC_locJ (hU : SameUlocJ hi S Uloc) (hB : FrRatJ t B) (hTc : HypTJC t) : LocHypC S (locJ hi t B) := by
  refine locHypC_of (rankN D (i + 1) hi) (locJ hi t B) S B rfl Uloc hU ?_
  intro v x0 hx0
  have hfr := hB _ ((X.g u w hg).pl v).2
  obtain ⟨h1, h2⟩ := hTc _ ((X.g u w hg).pl v).2 x0 hx0
  rw [hfr] at h1 h2
  exact ⟨h1, h2⟩

end LocJ

section Mu

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def ClsPt (K : KerLabelsMu Tw u μ w h Lv) (st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))) : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) (β : (st j hj).Ch) (a : (st j hj).cmpt β) (L : (Fl.Pj (j + 1)).Tup)
    (g : ∀ v, GL (Fin ((Fl.Pj (j + 1)).m + 1)) ((Fl.Pj (j + 1)).Qq v)),
    (∀ v, L v = colSpan ((Fl.Pj (j + 1)).W v) (g v : Matrix (Fin ((Fl.Pj (j + 1)).m + 1)) (Fin ((Fl.Pj (j + 1)).m + 1))
      ((Fl.Pj (j + 1)).Qq v))) →
    ∀ (c : {c // (st j hj).chOf c = β}) (γ₀ : GL (Fin (D.R.N (j + 1))) D.host.E) (κ₀ : ((st j hj).K β).lev.U),
      γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) →
      ((st j hj).loc β).IsPt a g
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀ * (((st j hj).K β).y c).1 * κ₀.1) →
      K.cls (j + 1) ((st j hj).eC ⟨β, a⟩) L = c.1

end Mu

end Formalism.MainNotions.G.CmpJ.PStabEq

end

import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.mem b).outSec

abbrev rep (c : F.Cl) : F.D c.1 := (F.mem c.1).outSec.rep c.2

def valAt (φ : F.Forms) (c : F.Cl) : F.V := ((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) (F.rep c)

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

def pairAt (v : InfinitePlace K) (x y : F.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (F.bV.repr x i)) * v.embedding (F.gramV i j) * v.embedding (F.bV.repr y j)

def ipAt (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) : ℂ :=
  letI : Fintype F.Cl := h.fintypeCl
  ∑ c : F.Cl, (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ * F.pairAt v (F.valAt φ c) (F.valAt ψ c)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

def Free : Prop := ∀ b, (F.mem b).Free

abbrev hDim (h : F.Ok) : ℕ := (F.toCSD h).dim

def hB (h : F.Ok) : Basis (Fin (F.hDim h)) K F.Forms := (F.toCSD h).basis.map (F.res h).symm

abbrev hGram (h : F.Ok) : Matrix (Fin (F.hDim h)) (Fin (F.hDim h)) K := (F.toCSD h).H

def PosH (h : F.Ok) : Prop := ∀ v : InfinitePlace K, ((F.hGram h).map v.embedding).PosDef

@[reducible] def toH (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K where
  V := F.Forms
  ι := Fin (F.hDim h)
  b := F.hB h
  X := stdFrame (F.hGram h)
  L := L

abbrev hCoord (h : F.Ok) : F.Forms ≃ₗ[K] (Fin (F.hDim h) → K) := F.coordOf h F.outSec

def toHc (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : HLat K :=
  toHLat (stdFrame (F.hGram h)) (L.map ((F.hCoord h).toLinearMap.restrictScalars (𝓞 K)))

def delHc (h : F.Ok) : HLat K := toHLat (stdFrame (F.hGram h)) (F.toCSD h).delLat

def nabHc (h : F.Ok) : HLat K := toHLat (stdFrame (F.hGram h)) (F.toCSD h).nabLat

def subZ (h : F.Ok) (U : Submodule K F.Forms) : Submodule K (Fin (F.hDim h) → K) :=
  U.map (F.hCoord h).toLinearMap

def subEq (h : F.Ok) (U : Submodule K F.Forms) : U ≃ₗ[K] F.subZ h U := (F.hCoord h).submoduleMap U

abbrev subD (h : F.Ok) (U : Submodule K F.Forms) : ℕ := subDim (F.subZ h U)

def subB (h : F.Ok) (U : Submodule K F.Forms) : Basis (Fin (F.subD h U)) K U :=
  (subBasis (F.subZ h U)).map (F.subEq h U).symm

def subMat (h : F.Ok) (U : Submodule K F.Forms) : Matrix (Fin (F.hDim h)) (Fin (F.subD h U)) K :=
  subE (F.subZ h U)

@[reducible] def subH (h : F.Ok) (U : Submodule K F.Forms) (L : Submodule (𝓞 K) U) : HLat K where
  V := U
  ι := Fin (F.subD h U)
  b := F.subB h U
  X := restrFrame (F.subMat h U) (F.hGram h)
  L := L

def subIncl (h : F.Ok) (U : Submodule K F.Forms) (L : Submodule (𝓞 K) U) (L' : Submodule (𝓞 K) F.Forms) :
    (F.subH h U L).V →ₗ[K] (F.toH h L').V := U.subtype

def isoMat (h : F.Ok) (U : Submodule K F.Forms) (v : InfinitePlace K) :
    Matrix (Fin (F.hDim h)) (Fin (F.subD h U)) ℂ :=
  (stdFrame (F.hGram h) v)⁻¹ * (F.subMat h U).map v.embedding * restrFrame (F.subMat h U) (F.hGram h) v

theorem wt_eq_card (h : F.Ok) (c : F.Cl) :
    (F.toCSD h).wt c = Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) :=
  (F.mem c.1).wt_eq (h c.1) (F.mem c.1).outSec c.2

theorem ipAt_eq_sum (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) :
    F.ipAt h v φ ψ = ∑ b, (F.mem b).ipAt (h b) v (φ b) (ψ b) := by
  let _ : ∀ b, Fintype (F.mem b).Cl := fun b => (h b).fintypeCl
  unfold ipAt GSD.ipAt
  rw [Fintype.sum_sigma]
  rfl

variable {F} in
theorem Rat.mem (R : F.Rat) (b : F.β) : (F.mem b).Rat := ⟨R.pair_rat, R.act_rat b, R.pos⟩

theorem Rat.of_mem [Nonempty F.β] (R : ∀ b, (F.mem b).Rat) : F.Rat :=
  ⟨(R (Classical.arbitrary F.β)).pair_rat, fun b => (R b).act_rat, (R (Classical.arbitrary F.β)).pos⟩

variable {F} in
theorem Rat.toCSDOf (R : F.Rat) (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : (F.toCSDOf h s).Rat where
  pair_rat := R.pair_rat
  act_rat := fun c γ i j => R.act_rat c.1 (γ : F.G c.1) i j
  pos := R.pos

theorem hB_equivFun (h : F.Ok) (φ : F.Forms) : (F.hB h).equivFun φ = F.hCoord h φ := by
  funext i
  simp [hB, coordOf, res]

theorem hB_apply (h : F.Ok) (i : Fin (F.hDim h)) : F.res h (F.hB h i) = (F.toCSD h).basis i := by
  simp [hB]

theorem subB_equivFun (h : F.Ok) (U : Submodule K F.Forms) (x : U) :
    (F.subMat h U).mulVec ((F.subB h U).equivFun x) = F.hCoord h (x : F.Forms) := by
  unfold subMat
  rw [subE_mulVec]
  have : (F.subB h U).equivFun x = (subBasis (F.subZ h U)).equivFun (F.subEq h U x) := by
    funext i
    simp [subB]
  rw [this, LinearEquiv.symm_apply_apply]
  rfl

theorem subMat_injective (h : F.Ok) (U : Submodule K F.Forms) : Function.Injective (F.subMat h U).mulVec :=
  (subspace_image_spec K _ (F.subZ h U)).1

variable {F}

theorem PosH.frameOK {h : F.Ok} (hp : F.PosH h) (L : Submodule (𝓞 K) F.Forms) : FrameOK (F.toH h L) :=
  fun v => (frameOfSpec _ _ (hp v)).1

theorem PosH.met {h : F.Ok} (hp : F.PosH h) (v : InfinitePlace K) :
    metOf (stdFrame (F.hGram h) v) = (F.hGram h).map v.embedding := (frameOfSpec _ _ (hp v)).2

theorem PosH.sub_maj {h : F.Ok} (hp : F.PosH h) (U : Submodule K F.Forms) (v : InfinitePlace K) (x y : U) :
    majAt (F.subB h U) (restrFrame (F.subMat h U) (F.hGram h)) v x y =
      majAt (F.hB h) (stdFrame (F.hGram h)) v (x : F.Forms) (y : F.Forms) := by
  rw [thl_majAt_coord (F.subB h U), thl_majAt_coord (F.hB h),
    (restrFrameSpec K _ _ (F.hGram h) hp (F.subMat h U) (F.subMat_injective h U) v).2.2,
    subB_equivFun, subB_equivFun, hB_equivFun, hB_equivFun]

theorem PosH.sub_norm {h : F.Ok} (hp : F.PosH h) (U : Submodule K F.Forms) (v : InfinitePlace K) (x : U) :
    normAt (F.subB h U) (restrFrame (F.subMat h U) (F.hGram h)) v x =
      normAt (F.hB h) (stdFrame (F.hGram h)) v (x : F.Forms) := by
  rw [normAt_eq_sqrt, normAt_eq_sqrt, hp.sub_maj]

variable (F)

def isoHc (h : F.Ok) (L : Submodule (𝓞 K) F.Forms) : Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (F.toH h L) (F.toHc h L) where
  e := F.hCoord h
  map_L := rfl
  norm := fun v x => by
    show normAt (Pi.basisFun K (Fin (F.hDim h))) (stdFrame (F.hGram h)) v (F.hCoord h x) =
      normAt (F.hB h) (stdFrame (F.hGram h)) v x
    rw [thl_normAt_coord (F.hB h), hB_equivFun]

variable {F}

theorem PosH.good {h : F.Ok} (hp : F.PosH h) {L : Submodule (𝓞 K) F.Forms} (hL : Submodule.IsLattice K L) :
    (F.toH h L).Good := ⟨hp.frameOK L, hL.fg, hL.span_eq_top⟩

theorem PosH.iso_sub {h : F.Ok} (hp : F.PosH h) (L : Submodule (𝓞 K) F.Forms) (U : Submodule K F.Forms) :
    ∃ I : Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (F.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))) (sub (F.toH h L) U),
      ∀ x : U, (I.e x : U) = x := by
  obtain ⟨I, hI⟩ := embIso' (F.subH h U (L.comap (U.subtype.restrictScalars (𝓞 K)))) (F.toH h L) U.subtype U
    (hp.frameOK L) (Submodule.injective_subtype U) (Submodule.range_subtype U) (fun v x => hp.sub_norm U v x) rfl
  exact ⟨I, fun x => Subtype.ext (hI x)⟩

variable (F)

theorem pairAt_add_left (v : InfinitePlace K) (x x' y : F.V) :
    F.pairAt v (x + x') y = F.pairAt v x y + F.pairAt v x' y := by
  simp only [pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (v : InfinitePlace K) (x y y' : F.V) :
    F.pairAt v x (y + y') = F.pairAt v x y + F.pairAt v x y' := by
  simp only [pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (v : InfinitePlace K) (a : K) (x y : F.V) :
    F.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * F.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (v : InfinitePlace K) (a : K) (x y : F.V) :
    F.pairAt v x (a • y) = v.embedding a * F.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem valAt_add (φ ψ : F.Forms) (c : F.Cl) : F.valAt (φ + ψ) c = F.valAt φ c + F.valAt ψ c := rfl

theorem valAt_smul (a : K) (φ : F.Forms) (c : F.Cl) : F.valAt (a • φ) c = a • F.valAt φ c := rfl

theorem isSesq_ipAt (h : F.Ok) : IsSesq (fun v (φ ψ : F.Forms) => F.ipAt h v φ ψ) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [ipAt, valAt_add, pairAt_add_left, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, valAt_add, pairAt_add_right, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, valAt_smul, pairAt_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · simp only [ipAt, valAt_smul, pairAt_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

def evRep (h : F.Ok) : F.Forms →ₗ[K] (F.Cl → F.V) := (F.toCSD h).Forms.subtype ∘ₗ (F.res h).toLinearMap

theorem evRep_apply (h : F.Ok) (φ : F.Forms) (c : F.Cl) : F.evRep h φ c = F.valAt φ c := rfl

theorem evRep_injective (h : F.Ok) : Function.Injective (F.evRep h) :=
  (Submodule.injective_subtype _).comp (F.res h).injective

theorem posAt_ipAt (h : F.Ok) (hpos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K F.Forms) :
    PosAt b (fun v (φ ψ : F.Forms) => F.ipAt h v φ ψ) := by
  classical
  intro v
  let _ : Fintype F.Cl := h.fintypeCl
  let P : F.Cl → Matrix F.ιV ι ℂ := fun c => Matrix.of fun i a => v.embedding (F.bV.repr (F.evRep h (b a) c) i)
  have hgram : gramOf b (fun (φ ψ : F.Forms) => F.ipAt h v φ ψ) =
      ∑ c, (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ • ((P c)ᴴ * F.gramV.map v.embedding * P c) := by
    ext a a'
    simp only [gramOf, Matrix.of_apply, ipAt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp only [pairAt, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply,
      Matrix.map_apply, evRep_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine thl_posDef_sum _ (fun c => ?_) _ (hpos v) P fun x hx => ?_
  · have : (0 : ℝ) < (((F.toCSD h).wt c : ℕ) : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (F.toCSD h).wt_pos c)
    have h2 : ((((F.toCSD h).wt c : ℕ) : ℝ)⁻¹ : ℂ) = (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ := by push_cast; rfl
    rw [← h2]
    exact_mod_cast this
  · let Bb : Basis (Σ _ : F.Cl, F.ιV) K (F.Cl → F.V) := Pi.basis fun _ => F.bV
    obtain ⟨g, hg⟩ := (F.evRep h).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (F.evRep_injective h))
    have h1 : (LinearMap.toMatrix Bb b g).map v.embedding * (LinearMap.toMatrix b Bb (F.evRep h)).map v.embedding = 1 := by
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
      simp
    have h2 : (LinearMap.toMatrix b Bb (F.evRep h)).map v.embedding *ᵥ x = 0 := by
      funext ⟨c, i⟩
      have := congrFun (hx c) i
      simpa [Matrix.mulVec, dotProduct, P, LinearMap.toMatrix_apply, Bb, Pi.basis_repr] using this
    have h3 := congrArg ((LinearMap.toMatrix Bb b g).map v.embedding).mulVec h2
    simpa [Matrix.mulVec_mulVec, h1] using h3

theorem pairAt_of_rat (v : InfinitePlace K) (x y : F.V) (hx : ∀ i, F.bV.repr x i ∈ cmMax K) :
    v.embedding (F.pair x y) = F.pairAt v x y := by
  conv_lhs => rw [← F.bV.sum_repr x, ← F.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, pairAt,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : v.embedding ((starRingEnd K) (F.bV.repr x i)) = starRingEnd ℂ (v.embedding (F.bV.repr x i)) :=
    hx i v.embedding
  rw [h1, RingHom.id_apply]
  simp only [gramV, Matrix.of_apply]
  ring

theorem gram_ipAt (h : F.Ok) (hr : (F.toCSD h).HasRatBasis) (v : InfinitePlace K) :
    gramOf (F.hB h) (fun (φ ψ : F.Forms) => F.ipAt h v φ ψ) = (F.hGram h).map v.embedding := by
  ext a a'
  simp only [gramOf, Matrix.of_apply, ipAt, Matrix.map_apply, CSD.H, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have e : ∀ a, F.valAt (F.hB h a) c = ((F.toCSD h).basis a : F.Cl → F.V) c := by
    intro a
    rw [← F.hB_apply h a]
    rfl
  rw [e, e]
  exact (F.pairAt_of_rat v _ _ fun i => (F.toCSD h).basis_rat hr a c i).symm

variable {F}

theorem Rat.posH (R : F.Rat) (h : F.Ok) : F.PosH h := by
  intro v
  rw [← F.gram_ipAt h (csd_hasRatBasis _ (R.toCSDOf h F.outSec)) v]
  exact F.posAt_ipAt h R.pos (F.hB h) v

theorem Rat.maj_eq (R : F.Rat) (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) :
    majAt (F.hB h) (stdFrame (F.hGram h)) v φ ψ = F.ipAt h v φ ψ := by
  rw [sesq_eq_sum (isSesq_maj (F.hB h) (stdFrame (F.hGram h))) (F.hB h) v φ ψ,
    sesq_eq_sum (F.isSesq_ipAt h) (F.hB h) v φ ψ, gramOf_maj,
    F.gram_ipAt h (csd_hasRatBasis _ (R.toCSDOf h F.outSec)) v]
  have := (R.posH h).met v
  unfold metOf at this
  rw [this]

theorem Rat.maj_eq_sum (R : F.Rat) (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) :
    majAt (F.hB h) (stdFrame (F.hGram h)) v φ ψ =
      ∑ b, majAt ((F.mem b).hB (h b)) (stdFrame ((F.mem b).hGram (h b))) v (φ b) (ψ b) := by
  rw [R.maj_eq h, F.ipAt_eq_sum]
  exact Finset.sum_congr rfl fun b _ => ((R.mem b).maj_eq (h b) v (φ b) (ψ b)).symm

end GFam

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

def intOf (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : Submodule (𝓞 K) F.Forms :=
  Submodule.pi Set.univ fun b => (F.mem b).intOf (N b)

theorem mem_intOf (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) (φ : F.Forms) :
    φ ∈ F.intOf N ↔ ∀ b d, ((φ b : (F.mem b).EqFun) : F.D b → F.V) d ∈ N b d := by
  unfold intOf
  rw [Submodule.mem_pi]
  exact ⟨fun H b => H b (Set.mem_univ b), fun H b _ => H b⟩

@[reducible] def withDel (N : ∀ b, F.D b → Submodule (𝓞 K) F.V) : GFam K := { F with Del := N }

end GFam

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem toFam_ok (h : S.Ok) : S.toFam.Ok := fun _ => h

theorem toFam_rat (R : S.Rat) : S.toFam.Rat := ⟨R.pair_rat, fun _ => R.act_rat, R.pos⟩

def famEq : S.toFam.Forms ≃ₗ[K] S.EqFun := LinearEquiv.funUnique Unit K S.EqFun

def famCl : S.toFam.Cl ≃ S.Cl := Equiv.uniqueSigma fun _ : Unit => S.Cl

theorem toFam_ipAt (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.toFam.Forms) :
    S.toFam.ipAt (S.toFam_ok h) v φ ψ = S.ipAt h v (S.famEq φ) (S.famEq ψ) := by
  rw [GFam.ipAt_eq_sum, Fintype.sum_unique]
  rfl

theorem toFam_map_intOf (N : S.D → Submodule (𝓞 K) S.V) :
    (S.toFam.intOf fun _ => N).map (S.famEq.toLinearMap.restrictScalars (𝓞 K)) = S.intOf N := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact (S.toFam.mem_intOf (fun _ => N) ψ).mp hψ ()
  · intro hφ
    exact ⟨S.famEq.symm φ, (S.toFam.mem_intOf (fun _ => N) _).mpr fun _ => hφ, rfl⟩

theorem toFam_map_intDel : S.toFam.intDel.map (S.famEq.toLinearMap.restrictScalars (𝓞 K)) = S.intDel :=
  S.toFam_map_intOf S.Del

theorem toFam_map_intNab : S.toFam.intNab.map (S.famEq.toLinearMap.restrictScalars (𝓞 K)) = S.intNab :=
  S.toFam_map_intOf S.Nab

def isoFamOf (R : S.Rat) (h : S.Ok) (L' : Submodule (𝓞 K) S.toFam.Forms) (L : Submodule (𝓞 K) S.EqFun)
    (hL : L'.map (S.famEq.toLinearMap.restrictScalars (𝓞 K)) = L) :
    Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (S.toFam.toH (S.toFam_ok h) L') (S.toH h L) where
  e := S.famEq
  map_L := hL
  norm := fun v x => by
    show normAt (S.hB h) (stdFrame (S.hGram h)) v (S.famEq x) =
      normAt (S.toFam.hB (S.toFam_ok h)) (stdFrame (S.toFam.hGram (S.toFam_ok h))) v x
    rw [normAt_eq_sqrt, normAt_eq_sqrt, R.maj_eq, (S.toFam_rat R).maj_eq, toFam_ipAt]

def isoFamDel (R : S.Rat) (h : S.Ok) :
    Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (S.toFam.toH (S.toFam_ok h) S.toFam.intDel) (S.toH h S.intDel) :=
  S.isoFamOf R h _ _ S.toFam_map_intDel

def isoFamNab (R : S.Rat) (h : S.Ok) :
    Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (S.toFam.toH (S.toFam_ok h) S.toFam.intNab) (S.toH h S.intNab) :=
  S.isoFamOf R h _ _ S.toFam_map_intNab

end GSD

section FormFam

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]

open Classical in

@[reducible] def formFam (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : β → LevFam X.E X.K n SG) : GFam X.K where
  β := β
  V := C.V
  ιV := VVIdx C.lam
  bV := C.bV
  pair := C.pair
  G b := FormG (Λ b)
  D _ := DecoSet X.E n ST SG
  actD b := formAct (Λ b)
  ρ b := formRho C (Λ b)
  Nab _ := C.Nab
  Del _ := C.Del

variable (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : β → LevFam X.E X.K n SG)

end FormFam

end Formalism.L2.Col

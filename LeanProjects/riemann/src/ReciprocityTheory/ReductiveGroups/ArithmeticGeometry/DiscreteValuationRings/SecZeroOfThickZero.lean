import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsAtScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemPowOfThickZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HrelPf

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem sec_zero_of_thick_zero' (hLB : lemmaBSt.{0}) (G : Over (Spec (CommRingCat.of V))) [GrpObj G]
    [hG : IsSemiAbelian G] (N : LB G.left) (hN : N.IsLB) (x : LB.Sec N)
    (hx : ∀ e i, ((fstG (maximalIdeal V) e G).left.app (N.U i)).hom (x.f i) = 0) : ∀ i, x.f i = 0 := by
  haveI := hG.comm
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI := hG.geomConnected
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine hLB V G N hN x ϖ hϖ fun i e => ?_
  rcases e with _ | e
  · simp
  · exact mem_pow_of_thick_zero' G ϖ hϖ _ _ e (hx e i)

set_option maxHeartbeats 1000000 in

theorem cross_global_of (hLaws : Laws) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))} (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ}
    (hCV : letI := H.starRing; ∀ (e : ℕ)
      (X : LB.Gen (LB.LinComb P.D.toPre.P.L ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left]
        ![((k * N : ℕ) : ℤ), -(k : ℤ)])), X.IsGen →
      ∀ (uR : LB.Gen (LB.LinComb P.D.toPre.P.L
        (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε)), uR.IsGen →
      LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A))
        (LB.oneGen P.D.toPre.P.L) →
      Function.Injective (fun χ : P.D.toPre.X => star a • χ) →
      ∀ (σ'' : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left)
          (fun _ => ((k * N : ℕ) : ℤ))))
        (τ : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))))
        (f'' : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α)
        (f : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB k α),
      (∀ i, P.U.ExpandsAt e (k * N) (σ'' i) (f'' i)) → (∀ i, P.U.ExpandsAt e k (τ i) (f i)) →
      (∀ i χ, ∃ u : LB.Gen (LB.LinComb P.D.toPre.P.L
          (Sum.elim (P.D.toPre.famφB (star a • χ)) (fun i => (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ i))
          (pullε k N)),
        u.IsGen ∧
        LB.Gen.Corr P.D.toPre.P.L _ _ _ _ u (LB.mulGen P.D.toPre.P.L _ _ _ _ X
          (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left)) ∧
        GeneratorPullback.SecRel P.D.toPre.P.L (P.D.toPre.famφB (star a • χ)) (DegPre.famε (k * N))
          (f'' i (star a • χ)) (P.D.toPre.famφB χ) (DegPre.famε k) (f i χ) (P.oD.onB.act a).left
          (Sum.elim (P.D.toPre.famφB (star a • χ)) (fun i => (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ i))
          (pullε k N) u) →
      (∀ i β, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' i β).f j = 0) →
      ∀ j, ((fstG (maximalIdeal V) e t.G).left.app _).hom
        ((mulSec P.U.LG.L _ _ _ _ (σ'' 0) (pullSec P.U.LG.L _ _ (τ 1) (t.act.act a).left)).f j -
          (mulSec P.U.LG.L _ _ _ _ (σ'' 1) (pullSec P.U.LG.L _ _ (τ 0) (t.act.act a).left)).f j) = 0)
    (s : Fin 2 → P.U.SecK k) (F : Fin 2 → Fam P.D.toPre (FractionRing V) k) (hs : ∀ i, P.U.Expands k (s i) (F i))
    (s'' : Fin 2 → P.U.SecK (k * N)) (F'' : Fin 2 → Fam P.D.toPre (FractionRing V) (k * N))
    (hs'' : ∀ i, P.U.Expands (k * N) (s'' i) (F'' i))
    (hPA : letI := H.starRing; ∀ i, PullAl P.D (FractionRing V) P.oD a k N (F i) (F'' i)) :
    ∀ j, (mulSec P.U.LG.L _ _ _ _ (s'' 0) (pullSec P.U.LG.L _ _ (s 1) (endK (t.act.act a)))).f j =
      (mulSec P.U.LG.L _ _ _ _ (s'' 1) (pullSec P.U.LG.L _ _ (s 0) (endK (t.act.act a)))).f j := by
  letI := H.starRing
  have hL : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  choose r hr σ f hsσ hsf hexp using hs
  choose r'' hr'' σ'' f'' hsσ'' hsf'' hexp'' using hs''
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXn⟩ := exists_XB P.D hL P.oD H.w0 uΨ huΨ a N hN hN0 k
  obtain ⟨uR, huR, huR0⟩ := exists_uR P.D P.oD a

  let σn : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((k * N : ℕ) : ℤ))) :=
    fun i => SecOps.secScale (scal t.G.hom (r i)) (σ'' i)
  let f''n : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α :=
    fun i α => SecOps.secScale (scal P.D.toPre.P.A.hom (r i)) (f'' i α)
  let τn : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))) :=
    fun i => SecOps.secScale (scal t.G.hom (r'' i)) (σ i)
  let fn : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB k α :=
    fun i α => SecOps.secScale (scal P.D.toPre.P.A.hom (r'' i)) (f i α)
  have hprB : (DegPre.prB P.D.toPre (FractionRing V)).left ≫ P.D.toPre.P.A.hom =
      (DegPre.BF P.D.toPre (FractionRing V)).hom := Over.w _
  have hgK : pullback.fst t.G.hom (jK V) ≫ t.G.hom = pullback.snd t.G.hom (jK V) ≫ jK V := pullback.condition
  have hfn : ∀ i α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε k)
      ((F i).s α) (P.D.toPre.famφB α) (DegPre.famε k) (fn i α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r i * r'' i)) := fun i α => by
    have := secScal_scale (hsf i α) (scal P.D.toPre.P.A.hom (r'' i))
    rwa [scal_pull _ _ _ hprB, ← scal_mul, mul_comm] at this
  have hf''n : ∀ i α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k * N))
      ((F'' i).s α) (P.D.toPre.famφB α) (DegPre.famε (k * N)) (f''n i α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r i * r'' i)) := fun i α => by
    have := secScal_scale (hsf'' i α) (scal P.D.toPre.P.A.hom (r i))
    rwa [scal_pull _ _ _ hprB, ← scal_mul] at this
  have hσn : ∀ i, GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => ((k * N : ℕ) : ℤ))
      (s'' i) (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => ((k * N : ℕ) : ℤ)) (σn i) (pullback.fst t.G.hom (jK V))
      (scal (pullback.snd t.G.hom (jK V) ≫ jK V) (r i * r'' i)) := fun i => by
    have := secScal_scale (hsσ'' i) (scal t.G.hom (r i))
    rwa [scal_pull _ _ _ hgK, ← scal_mul] at this
  have hτn : ∀ i, GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => (k : ℤ))
      (s i) (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => (k : ℤ)) (τn i) (pullback.fst t.G.hom (jK V))
      (scal (pullback.snd t.G.hom (jK V) ≫ jK V) (r i * r'' i)) := fun i => by
    have := secScal_scale (hsσ i) (scal t.G.hom (r'' i))
    rwa [scal_pull _ _ _ hgK, ← scal_mul, mul_comm] at this
  have hrel := fun i => hrel_integral_pf P.D hLaws.globalFns P.oD a N hN hN0 k X hX hXn uR huR huR0 (F i) (F'' i)
    (hPA i) (r i * r'' i) (fn i) (f''n i) (hfn i) (hf''n i)
  have hinj : Function.Injective (fun χ : P.D.toPre.X => star a • χ) :=
    fun _ _ h => smul_star_inj a N hN hN0 h
  have hexpn'' : ∀ e i, P.U.ExpandsAt e (k * N) (σn i) (f''n i) := fun e i =>
    expandsAt_scale P.U.toUnifPre e (k * N) (σ'' i) (f'' i) (r i) (hexp'' i e)
  have hexpn : ∀ e i, P.U.ExpandsAt e k (τn i) (fn i) := fun e i =>
    expandsAt_scale P.U.toUnifPre e k (σ i) (f i) (r'' i) (hexp i e)
  have hv := fun e => hCV e X hX uR huR huR0 hinj σn τn f''n fn (hexpn'' e) (hexpn e)
    (fun i χ => (hrel i).1 χ) (fun i => (hrel i).2)

  let C := SecOps.secAdd (mulSec P.U.LG.L _ _ _ _ (σn 0) (pullSec P.U.LG.L _ _ (τn 1) (t.act.act a).left))
    (SecOps.secNeg (mulSec P.U.LG.L _ _ _ _ (σn 1) (pullSec P.U.LG.L _ _ (τn 0) (t.act.act a).left)))
  haveI := t.semi
  have hC0 := sec_zero_of_thick_zero' hLaws.lemmaB t.G _ (linComb_isLB P.U.LG.L P.U.LG.isLB _ _) C
    (fun e j => by
      have := hv e j
      simpa [C, SecOps.secAdd, SecOps.secNeg, sub_eq_add_neg] using this)
  have hrK : ∀ i, r i * r'' i ≠ 0 := fun i => mul_ne_zero (hr i) (hr'' i)
  refine cross_to_K P.U.LG.L P.U.LG.isLB (t.act.act a) k (k * N) σn τn s'' s (fun i => r i * r'' i) hrK hσn hτn ?_
  intro j
  have := hC0 j
  simp only [C, SecOps.secAdd, SecOps.secNeg] at this
  exact (add_neg_eq_zero).1 this

end ReciprocityTheory.ChartRestriction.G.DVR

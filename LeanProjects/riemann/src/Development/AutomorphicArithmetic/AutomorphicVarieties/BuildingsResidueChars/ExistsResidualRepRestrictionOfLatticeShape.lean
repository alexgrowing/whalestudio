import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.LowAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.UpConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ConjFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ShapeQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.MuPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.KillQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

theorem UpperTheory.exists_residualRep_restriction_of_latticeShape :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Ok a → ∀ s : PD Unit (G ℚ Ω) k, LatShape D T.pr (resQ T.F T.g0) a s →
          ∃ s' : PD T.ι (G T.F Ω) k, (T.fr ∅).IsRes a s' ∧ T.OverQ s s' := by
  intro Ω _ _ _ l hl c D hD T hF k _ a _ _ P hS
  have hOk : T.Ok := hF.1
  have hP := hS.res.pair
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (a (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit (P.r x i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  have sh := fun v : T.ι => Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hP.low ()) hS.flag
  choose n hn hb using fun v : T.ι => Rq.luG k _ (P.r (g v)) (P.n ()) (hν (g v)) (hP.mult (g v)) (hP.low ())
    (sh v).1.1 (sh v).1.2
  let Q : PD T.ι (G T.F Ω) k := ⟨P.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj (Q.n v) * Q.r s * Q.n v) ∧
      ∀ i, Q.ψ v i s = P.ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ (P.r (g v)) (P.r ((g v)⁻¹ * resQ T.F s * g v)) (P.r (resQ T.F s)) _ _
      (hν (g v)) (hP.mult (g v)) (hP.low ()) (hn v) (hb v)
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hch : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), ∀ i, Q.ψ v i s = a (chi D T.pr i (resQ T.F s)) := fun v s hs i => by
    rw [(key v s hs).2, ← hconj (chi D T.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  refine ⟨Q, ⟨⟨fun x => hP.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ P.r hP.kill, hP.nrm, hn,
    fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩,
    ⟨fun x i => hS.res.res.diag (resQ T.F x) i, hch, Or.inl ⟨fun x => hS.supp _, fun v => (sh v).2 _ (hn v) (hb v)⟩⟩,
    fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, rfl, fun v => ⟨(), g v, hg v, hb v⟩⟩
  refine (hch v s hs.1 i).trans ?_
  rw [chi, Rq.muPs D hD T hOk _ s hs, Units.val_one, map_one]

import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PullbackDecomposition
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineAlgebraAlgebraMap
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TheoryEx
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumSecEqZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

private theorem bij_transport {ι X X' : Type*} {Y Y' : ι → Type*} (c : X ≃ X') (d : ∀ i, Y i ≃ Y' i)
    (g : ∀ i, X → Y i) (f : ∀ i, X' → Y' i) (h : ∀ i x, f i (c x) = d i (g i x))
    (hb : Function.Bijective fun x i => g i x) : Function.Bijective fun x i => f i x := by
  obtain ⟨hi, hs⟩ := hb
  refine ⟨fun x y hxy => ?_, fun b => ?_⟩
  · obtain ⟨x, rfl⟩ := c.surjective x
    obtain ⟨y, rfl⟩ := c.surjective y
    refine congrArg c (hi (funext fun i => (d i).injective ?_))
    have := congrFun hxy i
    simpa only [h] using this
  · obtain ⟨x, hx⟩ := hs fun i => (d i).symm (b i)
    refine ⟨c x, funext fun i => ?_⟩
    have := congrFun hx i
    simp only at this
    simp only [h, this, Equiv.apply_symm_apply]

private theorem sum_transport {W Y I : Type*} [AddCommGroup W] [AddCommGroup Y] [Fintype I] (a : I → ℤ) (e : Y ≃+ W)
    (f : I → Y) (g : I → W) (h : ∀ i, e (f i) = g i) (key : ∑ i, a i • g i = 0) : ∑ i, a i • f i = 0 := by
  apply e.injective
  rw [map_zero, map_sum]
  simp only [map_zsmul, h]
  exact key

variable {l : ℕ} [Fact l.Prime]

private theorem empty_isDec {A : Test l} (h : Subsingleton A.obj.A) :
    IsDec (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam A) := by
  refine ⟨fun x y _ => Subsingleton.elim x y, fun b => ⟨0, ?_⟩⟩
  funext e
  exact e.elim

private theorem locZero_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    {Q P : PAlg l ⥤ Type} {I : Type} [Fintype I] {a : I → ℤ} {u : I → (Q ⟶ P)} (hz : TZero a u) :
    Pa.LocZero (Q := testι l ⋙ Q) (P := testι l ⋙ P) a (fun i => Functor.whiskerLeft (testι l) (u i)) := by
  intro A y
  obtain ⟨S, hS, hs⟩ := hz A y
  refine ⟨S, (hPa A S).2 hS, fun s => ?_⟩
  rcases hs s with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((hPa _ _).2 (empty_isDec h0))

private theorem add_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    (n : ℕ) (hacr : AcrAdd) (F' : Coef (Test l)) (c : ∀ A, (testι l ⋙ AcrF l n).obj A ≃+ F'.obj A)
    (hc : ∀ {A B : Test l} (φ : A ⟶ B) (x : (testι l ⋙ AcrF l n).obj A),
      c B (((testι l ⋙ AcrF l n).map φ).hom x) = (F'.map φ).hom (c A x)) : Pa.Add F' := by
  intro A S hS
  exact bij_transport (c A).toEquiv (fun i => (c (S.B i)).toEquiv) (fun i x => PAlg.mapAcr (S.f i).hom n x)
    (fun i x => (F'.map (S.f i)).hom x) (fun i x => (hc (S.f i) x).symm) (hacr l n A S ((hPa A S).1 hS))

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.sumMH :
    UpperTheory.Ru.crystallineComparison.SumMH := by
  intro l _ Q P I _ a u hz n j x
  refine (partsEx l).elim fun Pa hPa => (theoryEx (Test l)).elim fun T hT => ?_
  refine (hT (Acris l) (testι l ⋙ AcrF l n)).elim fun F' h1 => h1.elim fun c h2 => h2.elim fun e h3 => ?_
  have hAdd : Pa.Add F' := add_of hPa n acrAdd F' c h3.1
  have key := locSum (Test l) Pa T F' hAdd (testι l ⋙ Q) (testι l ⋙ P) I a
    (fun i => Functor.whiskerLeft (testι l) (u i)) (locZero_of hPa hz) j
  have hp : ∀ i, e (testι l ⋙ Q) j (pullH (u i) n j x) =
      T.pull (Functor.whiskerLeft (testι l) (u i)) F' j (e (testι l ⋙ P) j x) := fun i =>
    h3.2 (Functor.whiskerLeft (testι l) (u i)) (pullMor (u i) n) rfl (fun _ _ => HEq.rfl) j x
  exact sum_transport a (e (testι l ⋙ Q) j) _ _ hp (key (e (testι l ⋙ P) j x))

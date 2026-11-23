import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AutomorphicArithmetic.WhittakerHecke.FirstChernClassEqZsmulOfLineUnitEqZpow
import Development.AutomorphicArithmetic.WhittakerHecke.ChernPowerZsmulEqPowSmul

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem inv_along {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E := by
  intro U hU
  obtain ⟨x⟩ := hU
  exact h U ⟨Sx.map f x⟩

private theorem pull_castHt {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi
  rfl

private theorem pull_cpow (hA : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E')
    (y : Ht q E' 2 1) (j : ℕ) : pull _ f _ _ (cpow q y j) = cpow q (pull _ f _ _ y) j := by
  obtain ⟨hcup, hone, -, -⟩ := hA q
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pull_castHt]
    congr 1
    exact hone f hE
  | succ k ih =>
    rw [cpow_succ, cpow_succ, pull_castHt]
    congr 1
    rw [hcup, ih]

private theorem inv_sch_of_is_unit (q : ℕ) (W : Scheme.{0}) (hq : IsUnit (q : Γ(W, ⊤))) : Inv q (sch.obj W) := by
  intro U hU
  obtain ⟨g⟩ := hU
  have g' : U ⟶ W := g
  have := hq.map (CommRingCat.Hom.hom (Scheme.Hom.appTop g'))
  simpa using this

theorem UpperTheory.firstChernClass_projBundle_line_of_twist_equiv :
    In → ∀ (q : ℕ) [NeZero q] {T W : Scheme.{0}} (r : T ⟶ W) (d : ℕ) {Ec Ee : Spc} (ac : Ec ⟶ sch.obj W) (ae : Ee ⟶ sch.obj T)
        (V : Ec ⟶ ofCat (glCat d)) (F : Ee ⟶ pullback V (PGL.pr d)),
        (∀ i : ℤ, Eqv _ ac (tw q i)) → (∀ i : ℤ, Eqv _ ae (tw q i)) → (∀ i : ℤ, Eqv _ F (tw q i)) →
        F ≫ pullback.fst V (PGL.pr d) ≫ ac = ae ≫ sch.map r → IsUnit (q : Γ(W, ⊤)) →
        ∀ (L : Ee ⟶ ofCat (glCat 1)) (ε : ℤˣ),
        (∀ (U : Scheme.{0}) (y : Sx Ee 1 U), lineUnit L y = lineUnit (F ≫ pullback.snd V (PGL.pr d) ≫ PGL.line d) y ^ (ε : ℤ)) →
        ∀ x : Ht q (sch.obj T) 2 1, pull _ ae _ 2 x = c1 q L → PBT q d r x := by
  intro hIn q _ T W r d Ec Ee ac ae V F hac hae hF hcomm hq L ε hL x hx
  obtain ⟨hcup, hone, hc1, -⟩ := hIn.a6nat q
  have iW := inv_sch_of_is_unit q W hq
  have iT : Inv q (sch.obj T) := inv_sch_of_is_unit q T (by
    simpa using hq.map (CommRingCat.Hom.hom (Scheme.Hom.appTop r)))
  have iEc : Inv q Ec := inv_along ac iW
  have iP : Inv q (pullback V (PGL.pr d)) := inv_along (pullback.fst V (PGL.pr d)) iEc
  have iEe : Inv q Ee := inv_along F iP
  have hxe : pull _ ae _ 2 x =
      (ε : ℤ) • pull _ F _ 2 (c1 q (pullback.snd V (PGL.pr d) ≫ PGL.line d)) := by
    rw [hx, UpperTheory.firstChernClass_eq_zsmul_of_lineUnit_eq_zpow hIn.a6add q L _ ε iEe hL, hc1 F _ iP]
  have hee : ∀ k : ℕ, ((ε : ℤ) ^ k) * ((ε : ℤ) ^ k) = 1 := by
    intro k
    rw [← mul_pow, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_pow]
  intro n i
  have hD := hIn.d1 q V iEc n i
  let G : (∀ j : Fin d, Ht q (sch.obj W) (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))) →
      (∀ j : Fin d, Ht q Ec (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))) :=
    fun a j => ((ε : ℤ) ^ (j : ℕ)) • pull _ ac _ _ (a j)
  have hG : Function.Bijective G := by
    constructor
    · intro a b hab
      funext j
      have e := congrFun hab j
      have e2 := congrArg (fun y => ((ε : ℤ) ^ (j : ℕ)) • y) e
      simp only [G, smul_smul, hee, one_smul] at e2
      exact (hac _ _).1 e2
    · intro b
      refine ⟨fun j => Function.surjInv (hac _ _).2 (((ε : ℤ) ^ (j : ℕ)) • b j), ?_⟩
      funext j
      simp only [G, Function.surjInv_eq, smul_smul, hee, one_smul]
  have key : ∀ a, pull _ ae _ n (∑ j : Fin d, Ht.cast (by omega) (by omega)
      ((cup q) (pull _ (sch.map r) (tw q (i - ((j : ℕ) : ℤ))) (n - 2 * ((j : ℕ) : ℤ)) (a j))
        (cpow q x (j : ℕ))) : Ht q (sch.obj T) n i) =
      pull _ F _ n (∑ j : Fin d, Ht.cast (by omega) (by omega)
      ((cup q) (pull _ (pullback.fst V (PGL.pr d)) (tw q (i - ((j : ℕ) : ℤ))) (n - 2 * ((j : ℕ) : ℤ)) (G a j))
        (cpow q (c1 q (pullback.snd V (PGL.pr d) ≫ PGL.line d)) (j : ℕ))) : Ht q _ n i) := by
    intro a
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pull_castHt, pull_castHt]
    congr 1
    rw [hcup, hcup, pull_cpow hIn.a6nat q ae iT, hxe, UpperTheory.chernPower_zsmul_eq_pow_smul, pull_cpow hIn.a6nat q F iP,
      ← pull_comp, ← hcomm, pull_comp, pull_comp]
    simp only [G, map_zsmul, AddMonoidHom.smul_apply]
  rw [← Function.Bijective.of_comp_iff' (hae i n)]
  convert (hF i n).comp (hD.comp hG) using 1
  funext a
  exact key a

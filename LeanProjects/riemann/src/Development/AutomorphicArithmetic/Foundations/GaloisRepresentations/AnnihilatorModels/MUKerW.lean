import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.uKerW_of :
    KerU → PullKer → UKerW := by
  intro hKerU _ p _ D O _ _ _ _ f b N r w _ hstd M j c T hflat X g hg
  obtain ⟨⟨k, hck⟩, hmon, hact, -, -, ψ', hmon', h1, h2⟩ := T.isog
  subst hck
  have hw : w ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  haveI : Smooth M.s := M.smooth.smooth
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsFinite T.s := T.fin
  haveI : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.s
  obtain ⟨hRep, -, hTors⟩ :=
    hKerU p D O b N r w hw hstd.ule T.Y (T.s ≫ M.s) T.o T.o' T.ψ ψ' k hmon hmon' hact h1 h2
  obtain ⟨K, i, -, -, hflatK, hiff⟩ := hRep
  have hiU : UKer r T.o T.ψ K i := (hiff K i).mp ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨y, rfl⟩ := (hiff X g).mpr hg
  intro a ha
  haveI := T.o.act.hom (algebraMap (𝓞 D.F) D.O a)
  have hpO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
    · exact h
  have hpowi : (i ≫ T.o.act.act (algebraMap (𝓞 D.F) D.O a)) ^ p ^ k = 1 := by
    have h := map_pow (IsMonHom.monoidHom (T.o.act.act (algebraMap (𝓞 D.F) D.O a)) K) i (p ^ k)
    change (i ^ p ^ k) ≫ _ = (i ≫ _) ^ p ^ k at h
    rw [← h, hTors K i hiU]
    exact map_one (IsMonHom.monoidHom (T.o.act.act (algebraMap (𝓞 D.F) D.O a)) K)
  have key : i ≫ T.o.act.act (algebraMap (𝓞 D.F) D.O a) = 1 := by
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hpowi
    apply OrdCount.eq_one_of_reg T.o.A T.o.ab _ (p ^ k)
    · intro U s hs
      haveI : Flat K.hom := hflatK
      haveI : Flat (T.s ≫ M.s) := hflat
      have hreg := pReg_of_flat (p := p) (K.hom ≫ T.s ≫ M.s) hpO U
      have hregk : ∀ n (t : Γ(K.left, U)), (p : Γ(K.left, U)) ^ n * t = 0 → t = 0 := by
        intro n
        induction n with
        | zero => intro t ht; simpa using ht
        | succ n ih =>
          intro t ht
          exact hreg _ (ih _ (by rw [← _root_.mul_assoc, ← _root_.pow_succ]; exact ht))
      push_cast at hs
      exact hregk k s hs
    · exact hpowi
    · intro k' _ _ hk z g'
      have hp' : (p : k') ≠ 0 := by
        intro h0
        apply hk
        push_cast
        rw [h0, zero_pow hk0]
      let φ : O →+* k' := (Spec.preimage (z ≫ T.s ≫ M.s)).hom
      haveI : CharZero k' := by
        apply charZero_of_injective_ringHom (f := φ)
        have hker : RingHom.ker φ = ⊥ := by
          by_contra hne
          have hmax := Ideal.IsPrime.isMaximal (RingHom.ker_isPrime φ) hne
          have heq := IsLocalRing.eq_maximalIdeal hmax
          have hmem : (p : O) ∈ RingHom.ker φ := heq ▸ hstd.pmem
          rw [RingHom.mem_ker, map_natCast] at hmem
          exact hp' hmem
        exact (RingHom.injective_iff_ker_eq_bot φ).mpr hker
      have hU : UKer r T.o T.ψ (Over.mk z) (g' ≫ i) := (hiff _ _).mp ⟨g', rfl⟩
      rw [← Category.assoc]
      exact (T.tj k' z).1 _ hU.1 hU.2 a ha
  rw [Category.assoc, key]
  simp

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Root
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.CohHomNatCastZero

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section Va

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

private theorem frobN_nat (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (f : X ⟶ X) (j : ℕ) :
    frobN p X h j ≫ f = f ≫ frobN p X h j := by
  induction j with
  | zero => exact (Category.id_comp f).trans (Category.comp_id f).symm
  | succ j ih =>
    show (GlobalTheory.VB.frob X p h ≫ frobN p X h j) ≫ f = f ≫ GlobalTheory.VB.frob X p h ≫ frobN p X h j
    rw [Category.assoc, ih, ← Category.assoc, GlobalTheory.VB.frob_naturality p h f h, Category.assoc]

private theorem frobN_succ' (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (j : ℕ) :
    frobN p X h (j + 1) = frobN p X h j ≫ GlobalTheory.VB.frob X p h := by
  show GlobalTheory.VB.frob X p h ≫ frobN p X h j = _
  exact (frobN_nat X h _ j).symm

private theorem smor_comp {A : Over (Sp k)} [GrpObj A] {σ τ : k →+* k} {ψ φ : A.left ⟶ A.left}
    (m : SMor A σ ψ) (n : SMor A τ φ) : SMor A (τ.comp σ) (φ ≫ ψ) := by
  have hc := GrpMor.comp m n
  rwa [← GlobalTheory.Cris.spMap_comp] at hc

private noncomputable def rho {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C) :
    Module.End k (primDR A) :=
  haveI := i.hom c
  primPull (dp0 k) (𝟙 _) (i.act c)

private theorem smor_act {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C) :
    SMor A (RingHom.id k) (i.act c).left := by
  haveI := i.hom c
  have hc := homMor (dp0 k) (𝟙 (Sp k)) (i.act c)
  unfold SMor
  rw [spMap_id]
  exact hc

private theorem pull_act {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    (m : SMor A (RingHom.id k) (i.act c).left) (x : primDR A) : m.pull x = rho i c x := rfl

private theorem pull_rho {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) (M : SMor A σ (ψ ≫ (i.act c).left))
    (x : primDR A) : m.pull (rho i c x) = M.pull x :=
  haveI := i.hom c
  GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) (i.act c)) m M (fun _ => rfl) rfl x

private theorem rho_pull {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) (M : SMor A σ ((i.act c).left ≫ ψ))
    (x : primDR A) : rho i c (m.pull x) = M.pull x :=
  haveI := i.hom c
  GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) (i.act c)) M (fun _ => rfl) rfl x

private theorem card_bound {C : Type} [CommRing C] (χ : C →+* k) {f j : ℕ}
    (hN : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) (hj0 : 0 < j) (hjf : j < f)
    (hc : ∀ c, χ c ^ p ^ j = χ c) : False := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : 1 < p ^ j := Nat.one_lt_pow hj0.ne' hp1
  have hcard : Nat.card χ.range = p ^ f := by
    rw [← hN]
    exact Nat.card_congr (RingHom.quotientKerEquivRange χ).toEquiv.symm
  have hfin : Finite χ.range := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hS : (χ.range : Set k).Finite := Set.finite_coe_iff.mp hfin
  have hZ : hS.toFinset.card = p ^ f := by
    rw [← Set.ncard_eq_toFinset_card _ hS, ← Nat.card_coe_set_eq]
    exact hcard
  have hsub : hS.toFinset.val ⊆ (Polynomial.X ^ (p ^ j) - Polynomial.X : Polynomial k).roots := by
    intro x hx
    have hx' : x ∈ (χ.range : Set k) := by
      rw [Finset.mem_val, Set.Finite.mem_toFinset] at hx
      exact hx
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hx'
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq)]
    simp [hc c]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hq, hZ] at hle
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp1 hjf))

private theorem rho_ringHom {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] {w : Ideal C} {f : ℕ}
    {π : Par p w f} {χ : C →+* k} {i : OAct C A} {F : Submodule k (primDR A)} {Φ : primDR A →+ primDR A}
    (hL : Lin p π χ (rho i) F Φ) (hk : (p : k) = 0) (c : C) (x : primDR A) :
    rho i ((p : C) * c) x = 0 := by
  have hn : ∀ n : ℕ, rho i (n : C) = (n : Module.End k (primDR A)) := by
    intro n
    induction n with
    | zero =>
      have h0 := hL.add 0 0
      simp only [add_zero] at h0
      simpa using h0
    | succ n ih => rw [Nat.cast_succ, hL.add, ih, hL.one, Nat.cast_succ]
  rw [hL.mul, Module.End.mul_apply, hn, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul k, hk,
    zero_smul]

private theorem sig_eq (hk : (p : k) = 0) {j : ℕ} {σ τ : k →+* k} (h1 : ∀ x, σ x ^ p ^ j = x)
    (h2 : ∀ x, τ x ^ p ^ j = x) : τ = σ := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hk
  haveI : ExpChar k p := ExpChar.prime Fact.out
  ext x
  apply (iterateFrobenius k p j).injective
  simp only [iterateFrobenius_def]
  rw [h1, h2]

private theorem pull_congr {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ ψ' : A.left ⟶ A.left}
    (e : ψ = ψ') (m : SMor A σ ψ) (m' : SMor A σ ψ') (x : primDR A) : m.pull x = m'.pull x := by
  subst e; rfl

private theorem smor_right {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) : SMor A σ (ψ ≫ (i.act c).left) := by
  haveI := i.hom c
  have hc := GrpMor.comp (homMor (dp0 k) (𝟙 (Sp k)) (i.act c)) m
  rwa [RingHom.comp_id, Category.comp_id] at hc

private theorem smor_left {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) : SMor A σ ((i.act c).left ≫ ψ) := by
  haveI := i.hom c
  have hc := GrpMor.comp m (homMor (dp0 k) (𝟙 (Sp k)) (i.act c))
  rwa [RingHom.id_comp, Category.id_comp] at hc

private theorem frob_pull (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] {σ : k →+* k}
    {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) (z : primDR A) :
    frobDR p k hk A (m.pull z) = m.pull (frobDR p k hk A z) := by
  have F := frobMor p k hk A (cast_left p k hk A)
  have M := GrpMor.comp F m
  have e1 := GrpMor.pull_pull m F M
    (fun r => by simp only [RingHom.comp_apply, frobR_apply, map_pow])
    (GlobalTheory.VB.frob_naturality p _ ψ _) z
  have e2 := GrpMor.pull_pull F m M (fun _ => rfl) rfl z
  exact e1.trans e2.symm

private theorem kill (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] [IsReduced A.left]
    {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f) {χ : C →+* k} (i : OAct C A)
    (hL : Lin p π χ (rho i) (PrimitiveSubmodule A) (frobDR p k hk A).toAddMonoidHom)
    (hN : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) {j : ℕ} (hjf : j < f)
    {σ τ : k →+* k} {ψ V : A.left ⟶ A.left} (m : SMor A σ ψ) (n : SMor A τ V)
    (hσ : ∀ x, σ x ^ p ^ j = x) (hτ : ∀ x, τ x ^ p ^ j = x)
    (ha : frobN p A.left (cast_left p k hk A) j ≫ ψ = (i.act π.a).left)
    (hV : frobN p A.left (cast_left p k hk A) j ≫ V = (i.act ((p : C) ^ j)).left) :
    ∀ x ∈ PrimitiveSubmodule A, m.pull x = 0 := by
  have hst : σ = τ := (sig_eq hk hσ hτ).symm
  subst hst
  haveI := (UpperTheory.Gal.Ord.epi p A.left (cast_left p k hk A)).2 j
  have hcomm : ∀ c : C, (i.act c).left ≫ ψ = ψ ≫ (i.act c).left := by
    intro c
    apply Epi.left_cancellation (f := frobN p A.left (cast_left p k hk A) j)
    rw [← Category.assoc, frobN_nat A.left (cast_left p k hk A) (i.act c).left j, Category.assoc, ha,
      ← Category.assoc, ha, ← Over.comp_left, ← Over.comp_left, ← i.mul, ← i.mul, mul_comm c π.a]
  have hcom' : ∀ (c : C) (y : primDR A), rho i c (m.pull y) = m.pull (rho i c y) := by
    intro c y
    rw [rho_pull i c m (smor_left i c m) y, pull_rho i c m (smor_right i c m) y]
    exact pull_congr (hcomm c) _ _ y
  intro x hx
  have h2 : m.pull (rho i (1 - π.ε) x) = 0 := by
    have hpow : (p : C) ^ f * π.s = (p : C) ^ j * ((p : C) * ((p : C) ^ (f - j - 1) * π.s)) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← pow_succ, ← pow_add, show j + 1 + (f - j - 1) = f by omega]
    have e : ψ ≫ (i.act (1 - π.ε)).left = V ≫ (i.act ((p : C) * ((p : C) ^ (f - j - 1) * π.s))).left := by
      apply Epi.left_cancellation (f := frobN p A.left (cast_left p k hk A) j)
      rw [← Category.assoc, ha, ← Category.assoc, hV, ← Over.comp_left, ← Over.comp_left, ← i.mul,
        ← i.mul, π.away, hpow]
    rw [pull_rho i _ m (smor_right i (1 - π.ε) m) x,
      pull_congr e (smor_right i (1 - π.ε) m) (smor_right i ((p : C) * ((p : C) ^ (f - j - 1) * π.s)) n) x,
      ← pull_rho i _ n (smor_right i ((p : C) * ((p : C) ^ (f - j - 1) * π.s)) n) x,
      rho_ringHom hL hk _ x, map_zero]
  have h1 : m.pull (rho i π.ε x) = 0 := by
    by_cases hj : j = 0
    · subst hj
      have hσid : σ = RingHom.id k := RingHom.ext fun y => by simpa using hσ y
      subst hσid
      have hψ : ψ = (i.act π.a).left := (Category.id_comp ψ).symm.trans ha
      have hχa : χ π.a = 0 := by
        rw [← RingHom.mem_ker, hL.ker]
        exact π.mem
      rw [pull_congr hψ m (smor_act i π.a) _, pull_act i π.a (smor_act i π.a) _, hL.eig π.a x hx, hχa,
        zero_smul]
    · have hj0 : 0 < j := Nat.pos_of_ne_zero hj
      by_contra hne
      have hu : rho i π.ε x ∈ PrimitiveSubmodule A := hL.stab π.ε x hx
      have hu'F : m.pull (rho i π.ε x) ∈ PrimitiveSubmodule A := by
        rw [← hL.kerΦ]
        show frobDR p k hk A (m.pull (rho i π.ε x)) = 0
        rw [frob_pull hk m _]
        have h0 : frobDR p k hk A (rho i π.ε x) = 0 := (hL.kerΦ _).mpr hu
        rw [h0, map_zero]
      have hεu : rho i π.ε (m.pull (rho i π.ε x)) = m.pull (rho i π.ε x) := by
        rw [hcom', ← Module.End.mul_apply, ← hL.mul]
        obtain ⟨t, ht⟩ := π.idem
        have hee : π.ε * π.ε = (p : C) * t + π.ε := by rw [← ht]; ring
        rw [hee, hL.add, LinearMap.add_apply, rho_ringHom hL hk t x, zero_add]
      apply card_bound χ hN hj0 hjf
      intro c
      have h1c : rho i c (m.pull (rho i π.ε x)) = χ c • m.pull (rho i π.ε x) := by
        have h3 := hL.eig c _ hu'F
        rwa [hεu] at h3
      have h2c : rho i c (m.pull (rho i π.ε x)) = σ (χ c) • m.pull (rho i π.ε x) := by
        rw [hcom', hL.eig c x hx, map_smulₛₗ]
      have hsame : σ (χ c) = χ c := smul_left_injective k hne (h2c.symm.trans h1c)
      calc χ c ^ p ^ j = σ (χ c) ^ p ^ j := by rw [hsame]
        _ = χ c := hσ _
  have hdec : x = rho i π.ε x + rho i (1 - π.ε) x := by
    rw [← LinearMap.add_apply, ← hL.add, add_sub_cancel, hL.one, Module.End.one_apply]
  rw [hdec, map_add, h1, h2, add_zero]

private theorem vRoot [IsAlgClosed k] (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]
    (hab : IsAbelianScheme A) {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f)
    {χ : C →+* k} (i : OAct C A)
    (hL : Lin p π χ (rho i) (PrimitiveSubmodule A) (frobDR p k hk A).toAddMonoidHom) (j : ℕ) :
    ∃ (τ : k →+* k) (V : A.left ⟶ A.left), SMor A τ V ∧ (∀ x, τ x ^ p ^ j = x) ∧
      frobN p A.left (cast_left p k hk A) j ≫ V = (i.act ((p : C) ^ j)).left := by
  induction j with
  | zero =>
    refine ⟨RingHom.id k, (i.act 1).left, smor_act i 1, fun x => by simp, ?_⟩
    rw [pow_zero]
    exact Category.id_comp _
  | succ j ih =>
    obtain ⟨τ, V, n, hτ, hV⟩ := ih
    obtain ⟨σ1, ψ1, -, m1, hσ1, hψ1⟩ := root p k hk A hab (RingHom.id k) Function.bijective_id
      ((i.act (p : C)).left) (smor_act i (p : C)) (fun x _ => by
        rw [pull_act i _ (smor_act i (p : C)) x]
        have h0 := rho_ringHom hL hk 1 x
        rwa [_root_.mul_one] at h0)
    refine ⟨τ.comp σ1, V ≫ ψ1, smor_comp m1 n, fun x => ?_, ?_⟩
    · rw [RingHom.comp_apply, pow_succ', pow_mul, ← map_pow, hσ1, RingHom.id_apply, hτ]
    · rw [frobN_succ', Category.assoc, ← Category.assoc (GlobalTheory.VB.frob _ p _) V,
        GlobalTheory.VB.frob_naturality p (cast_left p k hk A) V (cast_left p k hk A), Category.assoc, hψ1,
        ← Category.assoc, hV, pow_succ, i.mul, Over.comp_left]

private theorem vaGen [IsAlgClosed k] (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]
    (hab : IsAbelianScheme A) {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f)
    {χ : C →+* k} (i : OAct C A)
    (hL : Lin p π χ (rho i) (PrimitiveSubmodule A) (frobDR p k hk A).toAddMonoidHom)
    (hN : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) :
    ∃ (σ : k →+* k) (ψ : A.left ⟶ A.left), Function.Bijective σ ∧ SMor A σ ψ ∧
      frobN p A.left (cast_left p k hk A) f ≫ ψ = (i.act π.a).left := by
  haveI : Smooth A.hom := IsAbelianScheme.smooth (self := hab)
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have key : ∀ j ≤ f, ∃ (σ : k →+* k) (ψ : A.left ⟶ A.left), Function.Bijective σ ∧ SMor A σ ψ ∧
      (∀ x, σ x ^ p ^ j = x) ∧ frobN p A.left (cast_left p k hk A) j ≫ ψ = (i.act π.a).left := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨RingHom.id k, (i.act π.a).left, Function.bijective_id, smor_act i π.a,
        fun x => by simp, Category.id_comp _⟩
    | succ j ih =>
      intro hj
      obtain ⟨σ, ψ, hσb, m, hσ, hψ⟩ := ih (by omega)
      obtain ⟨τ, V, n, hτ, hV⟩ := vRoot hk hab π i hL j
      have hk0 := kill hk π i hL hN (by omega : j < f) m n hσ hτ hψ hV
      obtain ⟨σ', ψ', hb', m', hσ', hψ'⟩ := root p k hk A hab σ hσb ψ m hk0
      refine ⟨σ', ψ', hb', m', fun x => ?_, ?_⟩
      · rw [pow_succ', pow_mul, hσ', hσ]
      · rw [frobN_succ', Category.assoc, hψ', hψ]
  obtain ⟨σ, ψ, hb, m, -, hψ⟩ := key f le_rfl
  exact ⟨σ, ψ, hb, m, hψ⟩

end Va

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.va :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∃ (σ : k →+* k) (ψ : o.A.left ⟶ o.A.left), Function.Bijective σ ∧ SMor o.A σ ψ ∧ frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left := by
  intro p _ D R _ b N hN3 hNp hm k _ _ hk β o i w f hker hnorm hf π
  have hL := UpperTheory.Gal.Ord.lin p D R b N hN3 hNp hm k hk β o i w f hker hnorm hf π
  have hC : Nat.card (𝓞 D.F ⧸ RingHom.ker (β.comp (b.t i))) = p ^ f := by
    rw [hker, ← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact vaGen hk o.ab π (o.act.toF D) hL hC

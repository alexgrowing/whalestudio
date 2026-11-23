import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestCharacter

theorem emb_pow (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Fintype F] [CharP F p] [Field k]
    (f g : F →+* k) : ∃ n : ℕ, ∀ a, g a = f a ^ p ^ n := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra F k := f.toAlgebra
  letI : Algebra (ZMod p) k := (f.comp (algebraMap (ZMod p) F)).toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : F →ₐ[ZMod p] k :=
    { g with
      commutes' := fun r => by
        have : g.comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) k := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun this r }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 (g'.restrictNormal F)
  refine ⟨n, fun a => ?_⟩
  have h1 := g'.restrictNormal_commutes F a
  have h2 := DFunLike.congr_fun hn a
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h2
  rw [← h2, map_pow] at h1
  exact h1.symm

theorem eq_of_root {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (q : ℕ)
    (hq : (q : R) ∈ IsLocalRing.maximalIdeal R) {x y : R} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue R x = IsLocalRing.residue R y) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y q
  rw [hx, hy] at h1
  have h2 : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 :=
    mul_right_cancel₀ (sub_ne_zero.2 hne) (by rw [h1, _root_.one_mul])
  have h3 := congrArg (IsLocalRing.residue R) h2
  rw [map_sum, map_one] at h3
  simp only [map_mul, map_pow, h] at h3
  rw [geom_sum₂_self] at h3
  have h4 : ((q : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact hq
  rw [h4, zero_mul] at h3
  exact zero_ne_one h3

theorem fund {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) {x y z : R}
    (hx : x ^ p ^ n = x) (hy : y ^ p ^ n = y) (hz : z ^ p ^ n = z)
    (h : z - x - y ∈ IsLocalRing.maximalIdeal R) : z - x - y ∈ Ideal.span {(p : R)} := by
  set d := z - x - y with hd
  have hz' : z = (x + y) + d := by rw [hd]; ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (x + y) d n
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp x y n
  rw [← hz', hz, hs, hx, hy] at hr
  obtain ⟨m, hm⟩ : ∃ m, p ^ n = m + 2 := by
    have := Nat.one_lt_pow hn hp.one_lt
    exact ⟨p ^ n - 2, by omega⟩
  have hu : IsUnit (1 - d ^ (m + 1)) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact Ideal.pow_mem_of_mem (IsLocalRing.maximalIdeal R) h _ (Nat.succ_pos m)
  have h1 : d * (1 - d ^ (m + 1)) ∈ Ideal.span {(p : R)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨x * y * s + (x + y) * d * r, ?_⟩
    rw [hm] at hr
    linear_combination hd - hr
  exact (Ideal.mul_unit_mem_iff_mem _ hu).1 h1

theorem core (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) {F : Type} [Field F] [Fintype F] [CharP F p] {Sg : Type}
    (τ₀ : Sg) (φ' : Sg → Sg) (ρ : Sg → F →+* IsLocalRing.ResidueField R) (χ : Sg → F →*₀ R)
    (hχ : ∀ τ a, IsLocalRing.residue R (χ τ a) = ρ τ a) (hφ : ∀ τ a, ρ (φ' τ) a = ρ τ a ^ p) :
    ∃ (σ' : MulChar F R) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = (σ' ^ p ^ ee τ) a) ∧
      ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : ((Fintype.card F : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hn, Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hp _ n.pos
  have hroot : ∀ τ a, χ τ a ^ Fintype.card F = χ τ a := fun τ a => by
    rw [← map_pow, FiniteField.pow_card]
  choose ee hee using fun τ => emb_pow p (ρ τ₀) (ρ τ)
  let σ' : MulChar F R :=
    { (χ τ₀).toMonoidHom with
      map_nonunit' := fun a ha => by
        have : a = 0 := by simpa using ha
        subst this
        exact map_zero (χ τ₀) }
  have hσ : ∀ a, σ' a = χ τ₀ a := fun _ => rfl
  have key : ∀ τ a, χ τ a = (σ' ^ p ^ ee τ) a := fun τ a => by
    rw [MulChar.pow_apply' _ (pow_ne_zero _ hpp.ne_zero), hσ, ← map_pow]
    refine eq_of_root _ hq (hroot _ _) (hroot _ _) ?_
    rw [hχ, hχ, hee, map_pow]
  refine ⟨σ', ee, fun a b => ?_, key, fun τ => ?_⟩
  · rw [hσ, hσ, hσ]
    refine fund hpp n.ne_zero (hn ▸ hroot _ _) (hn ▸ hroot _ _) (hn ▸ hroot _ _) ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, hχ, hχ, hχ, map_add]
    ring
  · ext a
    rw [← key, pow_succ, pow_mul, MulChar.pow_apply' _ hpp.ne_zero, ← key, ← map_pow]
    refine eq_of_root _ hq (hroot _ _) (hroot _ _) ?_
    rw [hχ, hχ, hφ, map_pow]

theorem overC (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [Field C] [Algebra O C]
    (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (hvp : v (p : C) < 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] {Sg : Type}
    (τ₀ : Sg) (φ' : Sg → Sg) (σ : Sg → F →+* IsLocalRing.ResidueField O) (χ : Sg → F →*₀ C)
    (hχ : ∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
      χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1)
    (hφ : ∀ τ a, σ (φ' τ) a = σ τ a ^ p) :
    ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧
      (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  have hunit : ∀ a : RC, v (a : C) = 1 → IsUnit a := fun a ha => by
    have h0 : (a : C) ≠ 0 := by
      intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
    refine IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, (hv _).2 (by rw [map_inv₀, ha, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  haveI : IsLocalRing RC := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases ((hv _).1 a.2).eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · exact Or.inr (hunit _ (v.map_one_sub_of_lt h))
  have hnu : ∀ x : RC, (∀ u ∈ RC, u * (x : C) ≠ 1) → x ∈ IsLocalRing.maximalIdeal RC := fun x hx hu => by
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    exact hx u u.2 (congrArg Subtype.val hu)
  have hp : (p : RC) ∈ IsLocalRing.maximalIdeal RC := hnu _ fun u hu h => by
    have h1 := congrArg v h
    rw [map_mul, map_one] at h1
    have h2 : v u * v ((p : RC) : C) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 hu) zero_le (by simpa using hvp)
    exact h2.ne h1
  have hmem : ∀ τ a, χ τ a ∈ RC := fun τ a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ τ a)
    have := RC.add_mem (hχ τ a o ho).1 (RC.algebraMap_mem o)
    simpa using this
  let χ' : Sg → F →*₀ RC := fun τ =>
    { toFun := fun a => ⟨χ τ a, hmem τ a⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
  have hdiff : ∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
      χ' τ a - algebraMap O RC o ∈ IsLocalRing.maximalIdeal RC := fun τ a o ho =>
    hnu _ (hχ τ a o ho).2
  haveI : IsLocalHom (algebraMap O RC) := ⟨fun o ho => by
    by_contra hno
    have h1 := hdiff τ₀ 0 o (by rw [map_zero, IsLocalRing.residue_eq_zero_iff]; exact hno)
    rw [map_zero, zero_sub, neg_mem_iff] at h1
    exact h1 ho⟩
  let ψ := IsLocalRing.ResidueField.map (algebraMap O RC)
  obtain ⟨σ', ee, h1, h2, h3⟩ := core p hp τ₀ φ' (fun τ => ψ.comp (σ τ)) χ' (fun τ a => by
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σ τ a)
    have h := hdiff τ a o ho
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h
    rw [h, RingHom.comp_apply, ← ho]
    rfl) (fun τ a => by rw [RingHom.comp_apply, RingHom.comp_apply, hφ, map_pow])
  exact ⟨σ', ee, h1, fun τ a => congrArg Subtype.val (h2 τ a), h3⟩

theorem inj_loc {A Ω O : Type} [CommRing A] [Field Ω] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime]
    [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] :
    Function.Injective (algebraMap O Ω) := by
  rw [injective_iff_map_eq_zero]
  intro o ho
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
  have h1 := congrArg (algebraMap O Ω) h
  rw [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at h1
  have ha : a = 0 := IsIntegralClosure.algebraMap_injective A ℤ Ω (by rw [map_zero]; exact h1.symm)
  rw [ha, map_zero] at h
  exact (IsLocalization.map_units O s).mul_left_eq_zero.1 h

theorem exists_lift {A Ω T : Type} [CommRing A] [Field Ω] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    [CommRing T] [Algebra.IsIntegral ℤ T] (f : T →+* Ω) : ∃ g : T →+* A, ∀ t, algebraMap A Ω (g t) = f t := by
  letI : Algebra T Ω := f.toAlgebra
  exact ⟨(IsIntegralClosure.lift ℤ A Ω (S := T) : T →ₐ[ℤ] A), fun t => IsIntegralClosure.algebraMap_lift ℤ A Ω t⟩

end PositivityTheory.Xgn.TestCharacter

theorem PositivityTheory.Xgn.test_character_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ _ _ _ b _ φ hφ A _ _ _ m _ _ O _ _ _ _ _ _ _ t₀ Sg _ e φ' F
    _ _ _ pq sc w σ hO _ G c' _ P i _ _ C _ _ _ _ RC hT χ hχ
  obtain ⟨⟨τ₀, -⟩, -, he, hsurj, hσ, -, ⟨-, -, hpO⟩, -⟩ := hO
  obtain ⟨-, ⟨v, hv, hvp⟩, -⟩ := hT
  refine PositivityTheory.Xgn.TestCharacter.overC p RC v hv hvp τ₀ φ' σ χ hχ fun τ a => ?_
  have hinj := PositivityTheory.Xgn.TestCharacter.inj_loc (Ω := Ω) (O := O) m
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.Xgn.TestCharacter.exists_lift (A := A)
    (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))
  let g : 𝓞 c.F →+* O := (algebraMap A O).comp g₀
  have hg : ∀ t, algebraMap O Ω (g t) = 𝔐.cst (t : c.F) := fun t => by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hg₀]; rfl
  obtain ⟨a, rfl⟩ := hsurj a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hint : ∀ s, IsIntegral ℤ (labelEmb c s a) := fun s =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom
  obtain ⟨o₁, h₁, h₁'⟩ := hσ (φ' τ) a
  obtain ⟨o₂, h₂, h₂'⟩ := hσ τ a
  obtain ⟨u₁, hu₁⟩ : ∃ u : 𝓞 c.F, (u : c.F) = labelEmb c (φ (e τ)) a := ⟨⟨_, hint (φ (e τ))⟩, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : 𝓞 c.F, (u : c.F) = labelEmb c (e τ) a := ⟨⟨_, hint (e τ)⟩, rfl⟩
  have hn := hφ ((IsLocalRing.maximalIdeal O).comap g) (Ideal.comap_isPrime _ _)
    (by rw [Ideal.mem_comap, map_natCast]; exact hpO) (e τ) a u₁ u₂ hu₁ hu₂
  have e₁ : g u₁ = o₁ := hinj (by rw [hg, h₁, he, hu₁]; rfl)
  have e₂ : g u₂ = o₂ := hinj (by rw [hg, h₂, hu₂]; rfl)
  rw [Ideal.mem_comap, map_sub, map_pow, e₁, e₂, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero] at hn
  rw [← h₁', ← h₂', hn]

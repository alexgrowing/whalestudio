import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj WithConv
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.GroupBplus GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChainPts.SysB.HT

theorem exists_extend {G G' K : Type} [CommGroup G] [CommGroup G'] [Field K] [IsAlgClosed K] (j : G →* G')
    (hj : Function.Injective j) (f : G →* Kˣ) : ∃ f' : G' →* Kˣ, ∀ g, f' (j g) = f g := by
  letI : DivisibleBy (Additive Kˣ) ℕ := divisibleByOfSMulRightSurj (Additive Kˣ) ℕ fun {n} hn a => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : K) (Nat.pos_of_ne_zero hn)
    have h0 : z ≠ 0 := fun h => a.toMul.ne_zero (by rw [← hz, h, zero_pow hn])
    exact ⟨Additive.ofMul (Units.mk0 z h0), congrArg Additive.ofMul (Units.ext hz)⟩
  letI : DivisibleBy (Additive Kˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨k, hk⟩ := (Module.Baer.of_divisible (Additive Kˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive j) (fun a b h => hj h) (MonoidHom.toAdditive f)
  exact ⟨MonoidHom.toAdditive.symm k, fun g => DFunLike.congr_fun hk (Additive.ofMul g)⟩

theorem primitive_map {A K : Type} [CommRing A] [IsDomain A] [Field K] {p : ℕ} [hp : Fact p.Prime] (h0 : (p : K) ≠ 0)
    (f : A →+* K) {ζ : A} (h : IsPrimitiveRoot ζ p) : IsPrimitiveRoot (f ζ) p := by
  refine (IsPrimitiveRoot.iff_orderOf).2 (orderOf_eq_prime (by rw [← map_pow, h.pow_eq_one, map_one]) fun h1 => h0 ?_)
  simpa [h1] using congrArg f (h.geom_sum_eq_zero hp.out.one_lt)

theorem muRoot_nsmul {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] (ε : (PDivGroup.mu p A).Tate) (n k : ℕ) :
    muRoot (k • ε) n = muRoot ε n ^ k := by
  induction k with
  | zero => rw [zero_smul, muRoot_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, muRoot_add, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {p : ℕ} [hp : Fact p.Prime] {X : Scheme.{0}}
  {tX : SAB H X} {A : Type} [CommRing A] {x : Sp A ⟶ X} {t : SAB H (Sp A)} {φ : t.G.left ⟶ tX.G.left}
  {GG : PDivGroup p A}

omit hp in

theorem exists_equiv (hφ : IsGrpPullback t.G tX.G x φ) (B : Type) [CommRing B] [Algebra A B] {y : Sp B ⟶ X}
    (hy : spMap (algebraMap A B) ≫ x = y) :
    ∃ Φ : (SpAlg A B ⟶ t.G) ≃* (Over.mk y ⟶ tX.G), ∀ z, (Φ z).left = z.left ≫ φ := by
  subst hy
  exact GlobalTheory.WeilTorsChar.exists_mulEquiv_points x tX.G t.G φ hφ (SpAlg A B)

omit hp in

theorem subset_abLocus (hφ : IsGrpPullback t.G tX.G x φ) {T : Scheme.{0}} (f : T ⟶ Sp A)
    (h : Set.range (f ≫ x) ⊆ abLocus tX.G) : Set.range f ⊆ abLocus t.G := by
  rintro _ ⟨q, rfl⟩ K _ _ s ⟨r, hr⟩
  have h1 := h ⟨q, rfl⟩ K (s ≫ x) ⟨r, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hr]⟩
  have h2 := (IsPullback.of_hasPullback t.G.hom s).paste_horiz hφ.1
  rw [← h2.isoPullback_hom_snd]
  infer_instance

variable {O : Type} [CommRing O] [Algebra A O] (φ) (θ : TorsionMap t.G GG)

def IsChi {n : ℕ} (c : TorsChar tX (spMap (algebraMap A O) ≫ x) (p ^ n)) (u : GG.A n) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] [Algebra A B] [IsScalarTower A O B]
    (w : Over.mk (spMap (algebraMap O B) ≫ spMap (algebraMap A O) ≫ x) ⟶ tX.G) (z : Tors t.G (p ^ n) B),
    w.left = z.1.left ≫ φ → (c.χ B w : B) = θ.pt n B z u

variable {φ}

omit hp in

theorem base (B : Type) [CommRing B] [Algebra O B] [Algebra A B] [IsScalarTower A O B] :
    spMap (algebraMap A B) ≫ x = spMap (algebraMap O B) ≫ spMap (algebraMap A O) ≫ x := by
  rw [GlobalTheory.HTMap.spc_assoc, ← IsScalarTower.algebraMap_eq]

theorem exists_chi (hφ : IsGrpPullback t.G tX.G x φ) {n : ℕ} (u : GG.A n) (hu : IsGroupLikeElem A u) (hun : u ^ p ^ n = 1) :
    ∃ c : TorsChar tX (spMap (algebraMap A O) ≫ x) (p ^ n), IsChi φ θ c u := by
  classical
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have un : ∀ (B : Type) [CommRing B] [Algebra A B] (z : Tors t.G (p ^ n) B), IsUnit (θ.pt n B z u) := fun B _ _ z =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, hun, map_one]) hq
  let χ : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B],
      (Over.mk (spMap (algebraMap O B) ≫ spMap (algebraMap A O) ≫ x) ⟶ tX.G) → Bˣ := fun B _ _ _ w =>
    letI := ((algebraMap O B).comp (algebraMap A O)).toAlgebra
    if h : ∃ z : Tors t.G (p ^ n) B, w.left = z.1.left ≫ φ then (un B h.choose).unit else 1
  have hχ : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] [i : Algebra A B] [IsScalarTower A O B]
      (w : Over.mk (spMap (algebraMap O B) ≫ spMap (algebraMap A O) ≫ x) ⟶ tX.G) (z : Tors t.G (p ^ n) B),
      w.left = z.1.left ≫ φ → (χ B w : B) = θ.pt n B z u := by
    intro B _ _ _ i _ w z hz
    obtain rfl : i = ((algebraMap O B).comp (algebraMap A O)).toAlgebra :=
      Algebra.algebra_ext _ _ fun a => IsScalarTower.algebraMap_apply A O B a
    letI := ((algebraMap O B).comp (algebraMap A O)).toAlgebra
    have h : ∃ z : Tors t.G (p ^ n) B, w.left = z.1.left ≫ φ := ⟨z, hz⟩
    have e : h.choose = z := Subtype.ext (Over.OverMorphism.ext (hφ.1.hom_ext (h.choose_spec.symm.trans hz)
      ((Over.w _).trans (Over.w _).symm)))
    simp only [χ, dif_pos h, IsUnit.unit_spec, e]
  refine ⟨⟨χ, ?_, ?_⟩, fun B _ _ _ _ _ => hχ B⟩
  · intro B _ _ _ w w' hw hw'
    letI := ((algebraMap O B).comp (algebraMap A O)).toAlgebra
    haveI : IsScalarTower A O B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨Φ, hΦ⟩ := exists_equiv hφ B (base (O := O) B)
    obtain ⟨z, rfl⟩ := Φ.surjective w
    obtain ⟨z', rfl⟩ := Φ.surjective w'
    have h : z ^ p ^ n = 1 := Φ.injective (by rw [map_pow, hw, map_one])
    have h' : z' ^ p ^ n = 1 := Φ.injective (by rw [map_pow, hw', map_one])
    have h'' : (z * z') ^ p ^ n = 1 := by rw [mul_pow, h, h', _root_.one_mul]
    ext
    rw [Units.val_mul, ← map_mul, hχ B _ ⟨z, h⟩ (hΦ _), hχ B _ ⟨z', h'⟩ (hΦ _), hχ B _ ⟨_, h''⟩ (hΦ _)]
    exact (congrArg (fun f => f.ofConv u) (θ.mul n B ⟨z, h⟩ ⟨z', h'⟩ ⟨_, h''⟩ rfl)).trans (convMul_apply_groupLike _ _ hu)
  · intro B B' _ _ _ _ _ _ ψ w w' hw e
    letI := ((algebraMap O B).comp (algebraMap A O)).toAlgebra
    haveI : IsScalarTower A O B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := ((algebraMap O B').comp (algebraMap A O)).toAlgebra
    haveI : IsScalarTower A O B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨Φ, hΦ⟩ := exists_equiv hφ B (base (O := O) B)
    obtain ⟨z, rfl⟩ := Φ.surjective w
    have h : z ^ p ^ n = 1 := Φ.injective (by rw [map_pow, hw, map_one])
    have h' : (spOver (ψ.restrictScalars A) ≫ z) ^ p ^ n = 1 :=
      GlobalTheory.HTMap.tors_of (g := spMap ψ.toRingHom) (w := z) rfl h
    rw [hχ B _ ⟨z, h⟩ (hΦ _), hχ B' _ ⟨_, h'⟩ (by rw [e, hΦ]; exact (Category.assoc ..).symm),
      θ.nat n B B' (ψ.restrictScalars A) ⟨z, h⟩ ⟨_, h'⟩ rfl]
    rfl

theorem dlogIs {n : ℕ} {c : TorsChar tX (spMap (algebraMap A O) ≫ x) (p ^ n)} {u : GG.A n} (hc : IsChi φ θ c u)
    {c₁ : Pdiv.omega t.G →ₗ[A] Cot A (GG.A n)} (h₁ : θ.IsOmegaAt n c₁) (om : Pdiv.omega t.G) (hom₁ : dUnit A u = c₁ om)
    {g : ℕ} (v : Fin g → Pdiv.LieG t.G)
    (he : ∀ i, IsTanAtG tX (spMap (algebraMap A O) ≫ x) (spMap (dualMap (algebraMap A O)) ≫ (v i).1.left ≫ φ)) :
    DlogIs tX p n c (fun i => spMap (dualMap (algebraMap A O)) ≫ (v i).1.left ≫ φ)
      fun i => algebraMap A O (om.1 (v i)) := by
  obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X tX _ _ p n c g _ he
  have key : ∀ i, Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) (D i) =
      Ideal.Quotient.mk _ (algebraMap A O (om.1 (v i))) := fun i => by
    obtain ⟨w, hw⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : O) ^ n}) (he i)
    have h2 := hD _ _ (GlobalTheory.HTMap.comb_single he i) w hw
    have hle : Ideal.span {(p : A) ^ n} ≤ (Ideal.span {(p : O) ^ n}).comap (algebraMap A O) := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, map_natCast]
      exact Ideal.mem_span_singleton_self _
    let ψ : DualNumber (ModPow p A n) →ₐ[A] DualNumber (O ⧸ Ideal.span {(p : O) ^ n}) :=
      { dualMap (Ideal.quotientMap _ (algebraMap A O) hle) with
        commutes' := fun r => by
          ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'] }
    have h' : (spOver ψ ≫ (tanTors p n (v i)).1) ^ p ^ n = 1 :=
      GlobalTheory.HTMap.tors_of (g := spMap ψ.toRingHom) (w := (tanTors p n (v i)).1) rfl (tanTors p n (v i)).2
    rw [hc _ w ⟨_, h'⟩ ?_, θ.nat n _ _ ψ (tanTors p n (v i)) ⟨_, h'⟩ rfl] at h2
    · have h3 : ∀ z, (ψ z).snd = Ideal.quotientMap _ (algebraMap A O) hle z.snd := fun z => by simp [ψ, dualMap]
      rw [AlgHom.comp_apply, h3, h₁.2.2 _ om u hom₁, Ideal.quotientMap_mk] at h2
      rw [h2, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
      simp
    · rw [hw]
      change _ = (spMap _ ≫ spMap _ ≫ (v i).1.left) ≫ φ
      rw [GlobalTheory.HTMap.spc_assoc, GlobalTheory.HTMap.spc_assoc, Category.assoc]
      congr 2
      refine RingHom.ext fun r => ?_
      ext
      · simp [dualMap, ψ]
      · simp [dualMap, ψ, snd_epsTo]
        rfl
  intro a w hw w' hw'
  rw [hD a w hw w' hw']
  simp only [map_sum, map_mul, key]

theorem exists_comb [IsDomain A] {Dw : Datum H} {act : PDivGroup.Action (𝓞 E) GG} {pol : GG ≅ GG.dual}
    {θ : TorsionMap t.G GG} {ε : (PDivGroup.mu p A).Tate} {τ : Dw.La →+ GG.Tate} (hP : IsPropG Dw t GG act pol θ ε τ)
    (b : Module.Basis (Fin GG.height) ℤ Dw.La) (K : Type) [Field K] [Algebra A K] (h0 : (p : K) ≠ 0)
    (hK : Set.range (spMap (algebraMap A K)) ⊆ abLocus t.G) (f : (SpAlg A K ⟶ t.G) →* Kˣ) :
    ∃ k : Fin GG.height → Fin p, ∀ z : Tors t.G (p ^ 1) K,
      (f z.1 : K) = θ.pt 1 K z (charElem (∑ j, (k j : ℕ) • (hP.constTate b).t' j) 1) := by
  have hb := hP.interior 1 K hK
  choose s hs using fun y : Dw.La => hb.2 (tatePt (τ y) 1 K)
  have hadd : ∀ y y', (s (y + y')).1 = (s y).1 * (s y').1 := fun y y' => by
    have h : ((s y).1 * (s y').1) ^ p ^ 1 = 1 := by rw [mul_pow, (s y).2, (s y').2, _root_.one_mul]
    refine congrArg Subtype.val (hb.1 (a₂ := ⟨_, h⟩) ?_)
    have h1 := θ.mul 1 K (s y) (s y') ⟨_, h⟩ rfl
    rw [hs, hs] at h1
    rw [hs, map_add]
    exact (congrArg ofConv (map_mul (ptsPush (GG.A 1) (Algebra.ofId A K)) ((τ y).conv 1) ((τ y').conv 1))).trans
      (congrArg ofConv h1.symm)
  have hζ := primitive_map h0 (algebraMap A K) (by simpa only [pow_one] using hP.prim 1 : IsPrimitiveRoot (muRoot ε 1) p)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  choose k hk hk' using fun j => hζ.eq_pow_of_pow_eq_one (ξ := (f (s (b j)).1 : K)) (by
    have h : (s (b j)).1 ^ p = 1 := by simpa only [pow_one] using (s (b j)).2
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h, map_one, Units.val_one])
  refine ⟨fun j => ⟨k j, hk j⟩, fun z => ?_⟩
  obtain ⟨y, hy⟩ := hP.onto 1 K h0 (θ.pt 1 K z)
  obtain rfl : z = s y := hb.1 (hy.symm.trans (hs y).symm)
  rw [hs]
  let χ := ∑ j, k j • (hP.constTate b).t' j
  let g₁ : Dw.La →+ Additive K := (MonoidHom.toAdditive (Units.coeHom K)).comp
    (AddMonoidHom.mk' (fun y => Additive.ofMul (f (s y).1)) fun y y' => by rw [hadd, map_mul, ofMul_mul])
  let g₂ : Dw.La →+ Additive K :=
    { toFun := fun y => Additive.ofMul (algebraMap A K (muRoot (pairing GG A (τ y) χ) 1))
      map_zero' := by rw [map_zero, map_zero, LinearMap.zero_apply, muRoot_zero, map_one, ofMul_one]
      map_add' := fun y y' => by rw [map_add, map_add, LinearMap.add_apply, muRoot_add, map_mul, ofMul_mul] }
  have hg : g₁ = g₂ := AddMonoidHom.eq_of_eqOn_dense (s := Set.range b)
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, b.span_eq]; rfl) (by
      rintro _ ⟨i, rfl⟩
      refine congrArg Additive.ofMul (((hk' i).symm.trans ?_ : (f (s (b i)).1 : K) = _))
      have h : pairing GG A (τ (b i)) χ = k i • ε := by
        rw [map_sum, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
        · rw [map_nsmul]
          exact congrArg _ (((hP.constTate b).pair i i).trans (if_pos rfl))
        · rw [map_nsmul]
          exact (congrArg _ (((hP.constTate b).pair i j).trans (if_neg hj.symm))).trans (smul_zero _)
      rw [h, muRoot_nsmul, map_pow])
  have h := congrArg Additive.toMul (DFunLike.congr_fun hg y)
  exact h.trans (congrArg (algebraMap A K) (muRoot_pairing _ _ 1))

theorem exists_comb_int [IsLocallyNoetherian X] [IsDomain A] (hφ : IsGrpPullback t.G tX.G x φ) {Dw : Datum H}
    {act : PDivGroup.Action (𝓞 E) GG} {pol : GG ≅ GG.dual}
    {θ : TorsionMap t.G GG} {ε : (PDivGroup.mu p A).Tate} {τ : Dw.La →+ GG.Tate} (hP : IsPropG Dw t GG act pol θ ε τ)
    (b : Module.Basis (Fin GG.height) ℤ Dw.La) (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [IsAlgClosed K]
    [CharZero K] [Algebra A ↥(intO K)]
    (hK : Set.range (spMap ((intO K).subtype.comp (algebraMap A ↥(intO K))) ≫ x) ⊆ abLocus tX.G)
    (c : TorsChar tX (spMap (algebraMap A ↥(intO K)) ≫ x) (p ^ 1)) :
    ∃ k : Fin GG.height → Fin p, IsChi φ θ c (charElem (∑ j, (k j : ℕ) • (hP.constTate b).t' j) 1) := by
  letI : Algebra A K := ((intO K).subtype.comp (algebraMap A ↥(intO K))).toAlgebra
  haveI : IsScalarTower A ↥(intO K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TorsCharExt.exists_hom_extend (GlobalTheory.TorsCharExt.intO_units_root K) (p ^ 1) (c.χ ↥(intO K))
    (c.mul ↥(intO K))
  obtain ⟨Φ, hΦ⟩ := exists_equiv hφ ↥(intO K) (base (O := ↥(intO K)) (x := x) ↥(intO K))
  let io : ↥(intO K) →ₐ[A] K := IsScalarTower.toAlgHom A _ _
  let j : (SpAlg A ↥(intO K) ⟶ t.G) →* (SpAlg A K ⟶ t.G) := Formalism.L2.Pj.preHom (spOver io)
  have hj : Function.Injective j := fun a a' h => by
    haveI := t.semi.separated
    haveI : AlgebraicGeometry.IsReduced (SpAlg A ↥(intO K)).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (CommRingCat.of ↥(intO K))))
    haveI : IsDominant (spMap (intO K).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      intro z hz
      have : z = 0 := Subtype.ext hz
      simp [this])⟩
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated t.G.hom ((Over.w a).trans (Over.w a').symm)
      (spMap (intO K).subtype) (congrArg Over.Hom.left h))
  obtain ⟨f, hf⟩ := exists_extend j hj ((Units.map (intO K).subtype.toMonoidHom).comp (f₀.comp Φ.toMonoidHom))
  obtain ⟨k, hk⟩ := exists_comb hP b K (Nat.cast_ne_zero.2 hp.out.ne_zero) (subset_abLocus hφ _ hK) f
  obtain ⟨c', hc'⟩ := exists_chi (O := ↥(intO K)) θ hφ _
    (isGroupLikeElem_charElem (∑ j, (k j : ℕ) • (hP.constTate b).t' j) 1) (charElem_pow_self _ 1)
  refine ⟨k, fun B _ _ _ _ _ w z hz => ?_⟩
  rw [← hc' B w z hz]
  refine congrArg Units.val (GlobalTheory.CharUniq.char_unique E H X tX K _ _ (pow_ne_zero _ hp.out.ne_zero) c c'
    (fun w hw => ?_) B w ?_)
  · obtain ⟨z, rfl⟩ := Φ.surjective w
    have h : z ^ p ^ 1 = 1 := Φ.injective (by rw [map_pow, hw, map_one])
    have h' : j z ^ p ^ 1 = 1 := by rw [← map_pow, h, map_one]
    have h1 := hk ⟨_, h'⟩
    rw [hf, θ.nat 1 _ _ io ⟨z, h⟩ ⟨_, h'⟩ rfl] at h1
    refine Units.ext (Subtype.ext ?_)
    rw [hc' _ _ ⟨z, h⟩ (hΦ z), ← hf₀ _ hw]
    exact h1
  · obtain ⟨Ψ, hΨ⟩ := exists_equiv hφ B (base (O := ↥(intO K)) (x := x) B)
    obtain rfl : w = Ψ z.1 := Over.OverMorphism.ext (hz.trans (hΨ _).symm)
    rw [← map_pow, z.2, map_one]

theorem htSt : HTSt := by
  intro E _ _ _ H Dw p hp X _ tX hX A _ _ x t φ hφ GG act pol θ ε τ hP n e b c hc om hom₁ g u hu C κ hab a v hv
  subst e
  letI := κ.toAlgebra
  have he := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map tX κ hu
  let T := hP.constTate (b.reindex (finCongr rfl))
  let s := (Fintype.equivFin (Fin GG.height → Fin p)).symm
  have hd : ∀ (k : Fin GG.height → Fin p) (χ : TorsChar tX (spMap κ ≫ x) (p ^ 1)),
      IsChi (O := ↥(intO ↥C.S)) φ θ χ (charElem (∑ j, (k j : ℕ) • T.t' j) 1) →
      DlogIs tX p 1 χ (fun i => spMap (dualMap κ) ≫ (u i).1.left ≫ φ)
        fun i => κ ((∑ j, (k j : ℕ) • om j).1 (u i)) := fun k χ h =>
    dlogIs θ h (hc 1) _ (by
      rw [← dlog_val, map_sum, map_sum]
      refine (map_sum (LinearMap.proj 1 ∘ₗ GG.omegaSub.subtype) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_nsmul, map_nsmul, map_nsmul]
      exact congrArg _ (hom₁ j).symm) u he.1
  have key := GlobalTheory.HTLevel.mem_latHT_iff HTBound.htBound E H X tX p C.S C.norm_p (spMap κ ≫ x)
    (GlobalTheory.LineNorm.WedgeMax.ext_intO hX _) g _ he _ (fun l i => κ ((∑ j, (s l j : ℕ) • om j).1 (u i)))
    (fun χ => by
      obtain ⟨k, hk⟩ := exists_comb_int hφ hP (b.reindex (finCongr rfl)) C.S hab χ
      obtain ⟨l, rfl⟩ := s.surjective k
      exact ⟨l, hd _ χ hk⟩)
    (fun l => (exists_chi (O := ↥(intO ↥C.S)) θ hφ _ (isGroupLikeElem_charElem (∑ j, (s l j : ℕ) • T.t' j) 1)
      (charElem_pow_self _ 1)).imp fun χ h => hd _ χ h) a v
    (by simpa only [GlobalTheory.LineNorm.WedgeMax.spMap_comp, GlobalTheory.LineNorm.WedgeMax.spMap_dual_comp, Category.assoc] using hv)
  rw [GlobalTheory.LineNorm.WedgeMax.spMap_comp, Category.assoc, key]
  refine and_congr_left fun _ => ?_
  have ev : ∀ k : Fin GG.height → Fin p, ∑ i, (κ ((∑ j, (k j : ℕ) • om j).1 (u i)) : ↥C.S) * a i =
      ∑ j, (k j : ℕ) • ∑ i, (κ ((om j).1 (u i)) : ↥C.S) * a i := fun k => by
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, AddSubmonoidClass.coe_nsmul, Pi.smul_apply, map_sum,
      map_nsmul, Finset.sum_mul, Finset.smul_sum, smul_mul_assoc]
    exact Finset.sum_comm
  simp only [ev]
  refine ⟨fun h j => ?_, fun h l => ?_⟩
  · have h1 := h (s.symm fun j' => if j' = j then ⟨1, hp.out.one_lt⟩ else ⟨0, hp.out.pos⟩)
    rw [Equiv.apply_symm_apply, Finset.sum_eq_single j (fun j' _ hj => by simp [hj]) (by simp)] at h1
    simpa using h1
  · exact (intO ↥C.S).sum_mem fun j _ => (intO ↥C.S).nsmul_mem (h j) _

end GlobalTheory.ChainPts.SysB.HT

end

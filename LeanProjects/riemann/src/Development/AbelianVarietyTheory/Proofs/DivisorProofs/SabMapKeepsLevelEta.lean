import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem toUnit_left_eq' {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom := by
  have := Over.w (toUnit T)
  simpa using this

theorem grpPullback_pow_succ {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ (n + 1)).left = (x ^ (n + 1)).left ≫ φ := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ x₀, pow_succ x]
    exact hφ.2 T _ _ _ _ ih hx

theorem eta_eq_etaA_pow {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {bb : Base (LowDat.lowLevel l) B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D (LowDat.lowLevel l) bb s) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β) (a : D.La)
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    toUnit (Over.mk x) ≫ o.eta a = (toUnit (Over.mk x) ≫ o.etaA a) ^ (l.M' / l.M) := by
  obtain ⟨-, I, -, hA, hM⟩ := o.geom k x β hx
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  have hM'0 : 0 < l.M' := Nat.lcm_pos hM0 l.A_pos
  have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd hM'0 hdvd) hM0
  have hmul : l.M * (l.M' / l.M) = (LowDat.lowLevel l).A := Nat.mul_div_cancel' hdvd
  rw [hM a ha, hA a, ← hmul]
  exact (I.tower l.M (l.M' / l.M) hM0 hq a).symm

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem sabMap_keeps_eta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (A W : Type) [CommRing A] [IsDomain A] [CommRing W] (bA : c.F →+* A) (b : c.F →+* W) (o' : LowObj D c bA) (o : LowObj D c b) (f : W →+* A), f.comp b = bA → ∀ m : SABMap o'.t o.t (spMap f), (∀ a, (o'.etaA a).left ≫ m.φ = spMap f ≫ (o.etaA a).left) → ∀ a, (o'.eta a).left ≫ m.φ = spMap f ≫ (o.eta a).left := by
  intro E _ _ _ H D l c A W _ _ _ bA b o' o f hf m hA a
  subst hf

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  have ha : u • a + v • a = a := by rw [← add_smul, huv, one_smul]
  have hu' : u • a ∈ (LowDat.lowLevel l).Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hu Submodule.mem_top
  have hv' : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have e1 : o'.eta a = o'.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o'.eta_add, o'.eta_ker _ hu', _root_.one_mul]
  have e2 : o.eta a = o.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o.eta_add, o.eta_ker _ hu', _root_.one_mul]
  rw [e1, e2]
  generalize v • a = a' at hv' ⊢

  let K := AlgebraicClosure (FractionRing A)
  let κ : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hκ : Function.Injective κ :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : IsDominant (spMap κ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical κ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hκ]; exact bot_le)⟩
  haveI := o.proper
  haveI : IsReduced (𝟙_ (Over (Sp A))).left := (inferInstance : IsReduced (Sp A))
  refine ext_of_isDominant_of_isSeparated o.t.G.hom ?_ (spMap κ) ?_
  · have w1 := Over.w (o'.eta a')
    have w2 := Over.w (o.eta a')
    have w3 := m.cart.1.w
    simp only [Category.assoc]
    rw [w3, ← Category.assoc, w1, w2]
    simp
  · let β : KA (LowDat.lowLevel l) →+* K := κ.comp ((f.comp b).comp (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    have hx' : spMap κ ≫ lowMap c (f.comp b) = spMap β := by
      unfold lowMap; rw [← Spec.map_comp]; rfl
    have hx : (spMap κ ≫ spMap f) ≫ lowMap c b = spMap β := by
      unfold lowMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
    have p' := eta_eq_etaA_pow o' K (spMap κ) β hx' a' hv'
    have p := eta_eq_etaA_pow o K (spMap κ ≫ spMap f) β hx a' hv'
    have hM0 : 0 < l.M := by have := l.three_le; omega
    have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
    have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd (Nat.lcm_pos hM0 l.A_pos) hdvd) hM0
    obtain ⟨n, hn⟩ : ∃ n, l.M' / l.M = n + 1 := ⟨l.M' / l.M - 1, by omega⟩
    rw [hn] at p p'
    have key := grpPullback_pow_succ m.cart (T := Over.mk (spMap κ)) (toUnit _ ≫ o'.etaA a')
      (toUnit (Over.mk (spMap κ ≫ spMap f)) ≫ o.etaA a') (by
        rw [Over.comp_left, Over.comp_left, toUnit_left_eq', toUnit_left_eq']
        simp only [Over.mk_hom, Category.assoc]
        rw [hA a']) n
    have q' := congrArg Over.Hom.left p'
    have q := congrArg Over.Hom.left p
    rw [Over.comp_left, toUnit_left_eq'] at q q'
    simp only [Over.mk_hom] at q q'
    rw [← Category.assoc, q', ← key, ← q, Category.assoc]

end GlobalTheory.UCanon

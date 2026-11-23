import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Act

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem comp_mulMon (f : A ⟶ A) [IsMonHom f] (x y : T ⟶ A) : (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_compMon (f : A ⟶ A) [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_padd (x : T ⟶ A) (f g : A ⟶ A) : x ≫ padd A f g = (x ≫ f) * (x ≫ g) := by
  simp only [padd]
  rw [← Category.assoc, comp_lift, Hom.mul_def]

variable {O : Type} [Ring O] (ρ : RingAct A O)

theorem act_add_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := by
  rw [ρ.map_add, comp_padd]

theorem act_mul_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a * b) = (x ≫ ρ.act b) ≫ ρ.act a := by
  rw [ρ.map_mul, Category.assoc]

theorem act_one_apply (x : T ⟶ A) : x ≫ ρ.act 1 = x := by
  rw [ρ.map_one, Category.comp_id]

theorem act_zero_apply (x : T ⟶ A) : x ≫ ρ.act 0 = 1 := by
  have h := act_add_apply ρ x 0 0
  rw [add_zero] at h
  exact (_root_.mul_left_cancel (a := x ≫ ρ.act 0) (by rw [_root_.mul_one]; exact h)).symm

theorem act_nat_apply (x : T ⟶ A) (n : ℕ) : x ≫ ρ.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_apply, _root_.pow_zero]
  | succ n ih => rw [Nat.cast_succ, act_add_apply, ih, act_one_apply, _root_.pow_succ]

theorem pow_eq_one_of_kill {a b : O} {N : ℕ} (hab : a * b = (N : O)) (x : T ⟶ A) (hx : x ≫ ρ.act b = 1) :
    x ^ N = 1 := by
  rw [← act_nat_apply ρ x N, ← hab, act_mul_apply, hx]
  haveI := ρ.hom a
  exact one_compMon (ρ.act a)

end Act

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro u v h
  apply Units.ext
  have h1 := congrArg (fun w : (Γ(Sp K, ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h1

section Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_nsmul_of_dvd (Dw : Datum H) (N : ℕ) (d : Dw.La)
    (h : ∀ b, (N : ℤ) ∣ Dw.EF b d) : ∃ f : Dw.La, d = N • f := by
  have skew : ∀ x y, Dw.EF x y = - Dw.EF y x := by
    intro x y
    have hxy := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at hxy
    linarith
  have hdiv : ∀ y, (N : ℤ) ∣ Dw.EF d y := fun y => by
    rw [skew]
    exact dvd_neg.mpr (h y)
  let φ : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF d y / N
      map_add' := fun y z => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hdiv y)
      map_smul' := fun m y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc _ (hdiv y) }
  obtain ⟨f, hf⟩ := Dw.unimod.2 φ
  refine ⟨f, Dw.unimod.1 (LinearMap.ext fun y => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hf]
  show Dw.EF d y = N • (Dw.EF d y / N)
  rw [nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv y)]

theorem sep_core (A : PolAV (Sp (FractionRing R))) : letI := H.starRing
    ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a)
        (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N : ℕ), 1 ≤ N →
      ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 →
      ∀ x x' : TFK (R := R) F ⟶ A.A, x ≫ oA.act (star β) = 1 → x' ≫ oA.act (star β) = 1 → x ≠ x' →
        ∃ z : TFK (R := R) F ⟶ A.A, z ≫ oA.act β = 1 ∧
          ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
            WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c' := by
  let _ := H.starRing
  intro oA Dw I N hN β u u' hβ huu x x' hx hx' hne
  have hN0 : 0 < N := hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev N (c • b) = I.ev N b ≫ oA.act c := fun c b => I.lin N c b
  obtain ⟨a, rfl⟩ := (I.onto N hN0 x).1 (pow_eq_one_of_kill oA.toRingAct hβ x hx)
  obtain ⟨a', rfl⟩ := (I.onto N hN0 x').1 (pow_eq_one_of_kill oA.toRingAct hβ x' hx')
  obtain ⟨e, he⟩ := (I.ker N hN0 (star β • a)).1 (by rw [hlin]; exact hx)
  obtain ⟨e', he'⟩ := (I.ker N hN0 (star β • a')).1 (by rw [hlin]; exact hx')
  have hdN : ∀ f : Dw.La, a - a' ≠ N • f := by
    intro f hf
    apply hne
    have : a = a' + N • f := by rw [← hf]; abel
    rw [this, I.add, (I.ker N hN0 _).2 ⟨f, rfl⟩, _root_.mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : Dw.La, ¬ ((N : ℤ) ∣ Dw.EF b0 (a - a')) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨f, hf⟩ := mem_nsmul_of_dvd Dw N (a - a') hcon
    exact hdN f hf
  have h1 : Dw.EF b0 (a - a') = Dw.EF ((u * β) • b0) (a - a') + Dw.EF ((u' * star β) • b0) (a - a') := by
    rw [← LinearMap.add_apply, ← map_add, ← add_smul, huu, one_smul]
  have h2 : (N : ℤ) ∣ Dw.EF ((u * β) • b0) (a - a') := by
    have hd' : H.bar (u * β) • (a - a') = N • (H.bar u • (e - e')) := by
      rw [map_mul, mul_smul, smul_sub]
      change H.bar u • (star β • a - star β • a') = _
      rw [he, he', ← smul_sub]
      exact smul_comm _ _ _
    rw [Dw.adj, hd', map_nsmul, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  have hb : ¬ (N : ℤ) ∣ Dw.EF ((u' * star β) • b0) (a - a') := fun h => hb0 (by rw [h1]; exact dvd_add h2 h)
  refine ⟨I.ev N ((u' * star β) • b0), ?_, ?_⟩
  · rw [← hlin, smul_smul, show β * (u' * star β) = (N : 𝓞 E) * u' by rw [← hβ]; ring, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact (I.ker N hN0 _).2 ⟨_, rfl⟩
  · refine ⟨unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a), unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a'),
      I.isom N hN0 _ _, I.isom N hN0 _ _, fun hc => hb ?_⟩
    have hc' := unitOn_injective hc
    rw [← (I.ζ_prim N hN0).zpow_eq_one_iff_dvd, map_sub, zpow_sub, hc', _root_.mul_inv_cancel]

end Sep

theorem alphaPair_holds : AlphaPairStatement := by
  intro E _ _ _ H V _ _ _ t P _ α N hN hαN hu _ F _ _ _ Dw I x x' hx hx' hne
  obtain ⟨u, u', hu⟩ := hu
  exact sep_core (H := H) (R := V) (F := F) P.A P.oA Dw I N hN α u u' hαN hu x x' hx hx' hne

end ReciprocityTheory.ChartRestriction.G.H1

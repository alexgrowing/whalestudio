import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Count

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

def killSub (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O) (ga : O) :
    Subgroup (TFK (R := R) F ⟶ A.A) :=
  letI := ρ.hom ga
  MonoidHom.ker (IsMonHom.monoidHom (ρ.act ga) (TFK (R := R) F))

theorem mem_killSub (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O) (ga : O)
    (x : TFK (R := R) F ⟶ A.A) : x ∈ killSub F A ρ ga ↔ x ≫ ρ.act ga = 1 := by
  first
    | exact Iff.rfl
    | exact MonoidHom.mem_ker
    | simp [killSub, MonoidHom.mem_ker]

theorem card_killSub_le (hW : WeilSt) (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O)
    (N : ℕ) (ga gb : O) (hga : ∀ x ∈ killSub F A ρ ga, x ^ N = 1) (hgb : ∀ z ∈ killSub F A ρ gb, z ^ N = 1)
    [Finite (killSub F A ρ ga)] [Finite (killSub F A ρ gb)]
    (sep : ∀ x ∈ killSub F A ρ ga, ∀ x' ∈ killSub F A ρ ga, x ≠ x' → ∃ z ∈ killSub F A ρ gb,
      ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
        WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c') :
    Nat.card (killSub F A ρ ga) ≤ Nat.card (killSub F A ρ gb) := by
  classical
  haveI : IsLocallyNoetherian (Sp (FractionRing R)) := by
    first
      | infer_instance
      | (unfold Sp; infer_instance)
  obtain ⟨hEx, hMul, -, -⟩ := hW (Sp (FractionRing R)) A N (TFK (R := R) F)
  have huniq : ∀ (z x : TFK (R := R) F ⟶ A.A) (hz : z ^ N = 1) (hx : x ^ N = 1)
      (c : Γ((TFK (R := R) F).left, ⊤)ˣ), WeilIs A.A A.L N z x c → c = (hEx z x hz hx).exists.choose :=
    fun z x hz hx c hc => (hEx z x hz hx).unique hc (hEx z x hz hx).exists.choose_spec
  let χ : killSub F A ρ ga → (killSub F A ρ gb →* Γ((TFK (R := R) F).left, ⊤)ˣ) := fun x =>
    MonoidHom.mk' (fun z => (hEx z.1 x.1 (hgb _ z.2) (hga _ x.2)).exists.choose) (fun z z' =>
      (huniq (z * z').1 x.1 (hgb _ (z * z').2) (hga _ x.2) _ (hMul _ _ _ _ _ (hEx z.1 x.1 (hgb _ z.2) (hga _ x.2)).exists.choose_spec
        (hEx z'.1 x.1 (hgb _ z'.2) (hga _ x.2)).exists.choose_spec)).symm)
  have hinj : Function.Injective χ := by
    intro x x' hxx
    by_contra hne
    obtain ⟨z, hz, c, c', hc, hc', hcc⟩ := sep x.1 x.2 x'.1 x'.2 (fun h => hne (Subtype.ext h))
    have e1 := huniq z x.1 (hgb z hz) (hga _ x.2) c hc
    have e2 := huniq z x'.1 (hgb z hz) (hga _ x'.2) c' hc'
    have e3 : χ x ⟨z, hz⟩ = χ x' ⟨z, hz⟩ := by rw [hxx]
    exact hcc (e1.trans (e3.trans e2.symm))
  let ψ : killSub F A ρ ga → (killSub F A ρ gb →* Γ((TFK (R := R) F).left, ⊤)) := fun x =>
    (Units.coeHom _).comp (χ x)
  have hψ : Function.Injective ψ := by
    intro x x' h
    apply hinj
    refine MonoidHom.ext fun z => Units.ext ?_
    exact congrArg (fun f => f z) h
  haveI : IsDomain Γ((TFK (R := R) F).left, ⊤) := by
    first
      | infer_instance
      | exact Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1
  have hli := (linearIndependent_monoidHom (killSub F A ρ gb) Γ((TFK (R := R) F).left, ⊤)).comp ψ hψ
  haveI := Fintype.ofFinite (killSub F A ρ ga)
  haveI := Fintype.ofFinite (killSub F A ρ gb)
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcard

def torsionEquiv (A : PolAV (Sp (FractionRing R))) {O : Type} [CommRing O] (ρ : RingAct A.A O) (N : ℕ)
    (α β u u' : O) (hab : α * β = (N : O)) (huu : u * α + u' * β = 1) :
    {y : TFK (R := R) F ⟶ A.A // y ^ N = 1} ≃ killSub F A ρ α × killSub F A ρ β where
  toFun y := (⟨y.1 ≫ ρ.act (u' * β), by
      have := ρ.hom u'
      rw [mem_killSub, ← act_mul_apply, show α * (u' * β) = u' * (N : O) by rw [← hab]; ring, act_mul_apply,
        act_nat_apply, y.2, one_compMon]⟩,
    ⟨y.1 ≫ ρ.act (u * α), by
      have := ρ.hom u
      rw [mem_killSub, ← act_mul_apply, show β * (u * α) = u * (N : O) by rw [← hab]; ring, act_mul_apply,
        act_nat_apply, y.2, one_compMon]⟩)
  invFun zw := ⟨zw.1.1 * zw.2.1, by
    have := ρ.hom (N : O)
    rw [← act_nat_apply ρ, comp_mulMon, act_nat_apply, act_nat_apply,
      pow_eq_one_of_kill ρ (show β * α = (N : O) by rw [mul_comm]; exact hab) _ zw.1.2,
      pow_eq_one_of_kill ρ hab _ zw.2.2, _root_.mul_one]⟩
  left_inv y := by
    apply Subtype.ext
    show y.1 ≫ ρ.act (u' * β) * y.1 ≫ ρ.act (u * α) = y.1
    rw [← act_add_apply, add_comm, huu, act_one_apply]
  right_inv zw := by
    obtain ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ := zw
    have hz' : z ≫ ρ.act (u * α) = 1 := by
      have := ρ.hom u
      rw [act_mul_apply, (mem_killSub F A ρ α z).1 hz, one_compMon]
    have hw' : w ≫ ρ.act (u' * β) = 1 := by
      have := ρ.hom u'
      rw [act_mul_apply, (mem_killSub F A ρ β w).1 hw, one_compMon]
    have hz2 : z ≫ ρ.act (u' * β) = z := by
      conv_rhs => rw [← act_one_apply ρ z, ← huu, act_add_apply, hz', _root_.one_mul]
    have hw2 : w ≫ ρ.act (u * α) = w := by
      conv_rhs => rw [← act_one_apply ρ w, ← huu, act_add_apply, hw', _root_.mul_one]
    have := ρ.hom (u' * β)
    have := ρ.hom (u * α)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (z * w) ≫ ρ.act (u' * β) = z
      rw [comp_mulMon, hz2, hw', _root_.mul_one]
    · show (z * w) ≫ ρ.act (u * α) = w
      rw [comp_mulMon, hz', hw2, _root_.one_mul]

end Count

theorem alphaBarEnum_holds (hW : WeilSt) (hM : MulNSt) : AlphaBarEnumStatement := by
  intro E _ _ _ H V _ _ _ t P hTor α N hN1 hαN huu hNV F _ _ _ Dw hI
  letI := H.starRing
  obtain ⟨u, u', huu⟩ := huu
  classical
  haveI : IsLocallyNoetherian (Sp (FractionRing V)) := by
    first
      | infer_instance
      | (unfold Sp; infer_instance)
  let ρ := P.oA.toRingAct
  have hNF : ((N : ℕ) : F) ≠ 0 := by
    have h1 := (hNV.map (algebraMap V (FractionRing V))).map (algebraMap (FractionRing V) F)
    simp only [map_natCast] at h1
    exact h1.ne_zero
  have hcardN := (hM (Sp (FractionRing V)) P.A N hN1).2.2.2.2 F (jFK (R := V) F) hNF
  have hkA : ∀ x ∈ killSub F P.A ρ α, x ^ N = 1 := fun x hx =>
    pow_eq_one_of_kill ρ (show star α * α = (N : 𝓞 E) by rw [mul_comm]; exact hαN) x hx
  have hkB : ∀ x ∈ killSub F P.A ρ (star α), x ^ N = 1 := fun x hx =>
    pow_eq_one_of_kill ρ hαN x hx
  let eqv := torsionEquiv F P.A ρ N α (star α) u u' hαN huu
  have htot : Nat.card {y : TFK (R := V) F ⟶ P.A.A // y ^ N = 1} =
      Nat.card (killSub F P.A ρ α) * Nat.card (killSub F P.A ρ (star α)) := by
    rw [Nat.card_congr eqv, Nat.card_prod]
  have hpos : Nat.card {y : TFK (R := V) F ⟶ P.A.A // y ^ N = 1} ≠ 0 := by
    rw [hcardN]
    exact pow_ne_zero _ (by omega)
  haveI hfin : Finite {y : TFK (R := V) F ⟶ P.A.A // y ^ N = 1} := Nat.finite_of_card_ne_zero hpos
  haveI : Finite (killSub F P.A ρ α × killSub F P.A ρ (star α)) := Finite.of_equiv _ eqv
  haveI : Finite (killSub F P.A ρ α) := Finite.prod_left (killSub F P.A ρ (star α))
  haveI : Finite (killSub F P.A ρ (star α)) := Finite.prod_right (killSub F P.A ρ α)
  have sep1 : ∀ x ∈ killSub F P.A ρ (star α), ∀ x' ∈ killSub F P.A ρ (star α), x ≠ x' →
      ∃ z ∈ killSub F P.A ρ α, ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
        WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c' := by
    intro x hx x' hx' hne
    obtain ⟨z, hz, rest⟩ := sep_core (F := F) P.A P.oA Dw hI N hN1 α u u' hαN huu x x' hx hx' hne
    exact ⟨z, hz, rest⟩
  have sep2 : ∀ x ∈ killSub F P.A ρ α, ∀ x' ∈ killSub F P.A ρ α, x ≠ x' →
      ∃ z ∈ killSub F P.A ρ (star α), ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
        WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c' := by
    intro x hx x' hx' hne
    have h1 : star α * star (star α) = (N : 𝓞 E) := by rw [star_star, mul_comm]; exact hαN
    have h2 : u' * star α + u * star (star α) = 1 := by rw [star_star, add_comm]; exact huu
    obtain ⟨z, hz, rest⟩ := sep_core (F := F) P.A P.oA Dw hI N hN1 (star α) u' u h1 h2 x x'
      (by rw [star_star]; exact hx) (by rw [star_star]; exact hx') hne
    exact ⟨z, hz, rest⟩
  have hle1 := card_killSub_le F hW P.A ρ N (star α) α hkB hkA sep1
  have hle2 := card_killSub_le F hW P.A ρ N α (star α) hkA hkB sep2
  have hc2 : Nat.card (killSub F P.A ρ (star α)) = N ^ P.A.g := by
    have hsq : Nat.card (killSub F P.A ρ (star α)) ^ 2 = (N ^ P.A.g) ^ 2 := by
      rw [sq, ← pow_mul, mul_comm P.A.g 2, ← hcardN, htot, le_antisymm hle2 hle1]
    exact Nat.pow_left_injective two_ne_zero hsq
  let ev := (Finite.equivFinOfCardEq hc2).symm
  obtain ⟨f, hToA, hsurj, -⟩ := hTor F (1 * N) (by omega)
  have hx1 : ∀ b, ((ev b).1) ^ (1 * N) = 1 := fun b => by
    rw [Nat.one_mul]
    exact hkB _ (ev b).2
  refine ⟨fun b => (hsurj _ (hx1 b)).choose, fun b => (ev b).1, fun b => ?_, fun b => (ev b).2, ?_, ?_⟩
  · exact (hToA _ _).2 (hsurj _ (hx1 b)).choose_spec.symm
  · exact Subtype.val_injective.comp ev.injective
  · intro y hy
    exact ⟨ev.symm ⟨y, hy⟩, by simp⟩

end ReciprocityTheory.ChartRestriction.G.H1

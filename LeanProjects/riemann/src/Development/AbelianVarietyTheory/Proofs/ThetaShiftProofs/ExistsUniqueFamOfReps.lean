import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamFree

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FamSec (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

abbrev multiples (D : DegPre R) (k : ℕ) : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range

theorem zero_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s (α + k • mu)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hG k mu α
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem zero_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s β).f j = 0 := by
  obtain ⟨mu, rfl⟩ := hβ
  exact zero_add_nsmul hG s α mu h

theorem zero_add_nsmul_iff (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X) :
    (∀ j, (s.s (α + k • mu)).f j = 0) ↔ ∀ j, (s.s α).f j = 0 :=
  ⟨zero_of_eq_add_nsmul hG s ⟨-mu, by rw [smul_neg, add_neg_cancel_right]⟩, zero_add_nsmul hG s α mu⟩

theorem eq_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s t : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : s.s α = t.s α) : s.s β = t.s β := by
  have h0 := zero_of_eq_add_nsmul hG (s + -t) hβ (fun j => by rw [add_f, neg_f, h, add_neg_cancel])
  refine SecOps.sec_ext fun j => ?_
  have := h0 j
  rw [add_f, neg_f, add_neg_eq_zero] at this
  exact this

theorem add_nsmul_inj {k : ℕ} (hk : 1 ≤ k) (ρ a b : D.X) (h : ρ + k • a = ρ + k • b) : a = b := by
  have h' : (k : ℤ) • a = (k : ℤ) • b := by
    rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
  exact smul_right_injective D.X (by omega : (k : ℤ) ≠ 0) h'

theorem exists_fam_single (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (ρ : D.X)
    (σ : FamSec D F k ρ) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 :=
  UUA.exists_fam_rep hG hB k ρ (add_nsmul_inj hk ρ) σ

theorem existsUnique_fam_of_reps (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) {C : Type*}
    (rep : C → D.X) (hrep : ∀ α : D.X, ∃! c, ∃ mu, rep c + k • mu = α) (σ : ∀ c, FamSec D F k (rep c)) :
    ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c := by
  choose cl hcl hcl' using hrep
  choose f hf _ using fun c => exists_fam_single hG hB hk (rep c) (σ c)
  have key : ∀ (α β : D.X) (c : C), cl β = c → (f (cl β)).s β = (f c).s β := by
    rintro α β c rfl; rfl
  refine ⟨⟨fun β => (f (cl β)).s β, fun mu α u hu hc => ?_⟩, fun c => ?_, fun s hs => ?_⟩
  · have e : cl (α + k • mu) = cl α := by
      obtain ⟨nu, hnu⟩ := hcl α
      exact (hcl' (α + k • mu) (cl α) ⟨nu + mu, by rw [smul_add, ← add_assoc, hnu]⟩).symm
    have := (f (cl α)).fe mu α u hu hc
    rw [← key α _ _ e] at this
    exact this
  · have e : cl (rep c) = c := (hcl' (rep c) c ⟨0, by rw [smul_zero, add_zero]⟩).symm
    exact (key (rep c) _ _ e).trans (hf c)
  · refine fam_ext fun α j => ?_
    have := eq_of_eq_add_nsmul hG s (f (cl α)) (hcl α) ((hs (cl α)).trans (hf (cl α)).symm)
    rw [this]

theorem mk_eq_mk_iff {k : ℕ} (α β : D.X) :
    (QuotientAddGroup.mk α : D.X ⧸ multiples D k) = QuotientAddGroup.mk β ↔ ∃ mu, α + k • mu = β := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨mu, h⟩
    exact ⟨mu, by rw [show k • mu = -α + β from h, add_neg_cancel_left]⟩
  · rintro ⟨mu, rfl⟩
    exact ⟨mu, by rw [neg_add_cancel_left]; rfl⟩

theorem existsUnique_fam (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k)
    (rep : D.X ⧸ multiples D k → D.X) (hrep : ∀ c, QuotientAddGroup.mk (rep c) = c)
    (σ : ∀ c, FamSec D F k (rep c)) : ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c :=
  existsUnique_fam_of_reps hG hB hk rep (fun α => ⟨QuotientAddGroup.mk α, (mk_eq_mk_iff _ _).1 (hrep _),
    fun c hc => (hrep c).symm.trans ((mk_eq_mk_iff _ _).2 hc)⟩) σ

theorem IsSecBasis.ne_zero {S : Scheme.{0}} {A T : Over S} [Nontrivial Γ(T.left, ⊤)] {N : LB (T ⊗ A).left} {m : ℕ}
    {b : Fin m → LB.Sec N} (hb : IsSecBasis N b) (i : Fin m) : ¬ ∀ j, (b i).f j = 0 := by
  classical
  intro h
  obtain ⟨r, -, hr⟩ := hb SecOps.secZero
  have h0 := hr 0 (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    simp only [Pi.zero_apply, map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero])
  have h1 := hr (Pi.single i 1) (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    refine (Finset.sum_eq_zero fun i' _ => ?_).symm
    by_cases e : i' = i
    · rw [e, h j, mul_zero]
    · rw [Pi.single_eq_of_ne e, map_zero, map_zero, MulZeroClass.zero_mul])
  have := congrFun (h1.trans h0.symm) i
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

theorem exists_sec_ne_zero (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ σ : FamSec D F k α, ¬ ∀ j, σ.f j = 0 := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  have : Nontrivial Γ((TF (R := R) F).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := IsSecBasis.ne_zero hb ⟨0, pow_pos (by omega) _⟩
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc])
    (pullMulSec (b ⟨0, pow_pos (by omega) _⟩) (𝟙 _) u hu)
  refine ⟨σ, fun h => hne fun j => ?_⟩
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e := (hσ _ (𝟙 _) y J hJ).trans (sval_pullMulSec _ _ _ hu _ y hJ)
  rw [UUA.sval_zero_of h _ y J (hJ.mem _ _), Category.id_comp] at e
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e.symm

theorem exists_fam_support (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ s : Fam D F k, ∀ β : D.X, (¬ ∀ j, (s.s β).f j = 0) ↔ ∃ mu, α + k • mu = β := by
  obtain ⟨σ, hσ⟩ := exists_sec_ne_zero (D := D) (F := F) hT hk α
  obtain ⟨s, rfl, hs⟩ := exists_fam_single hG hB hk α σ
  refine ⟨s, fun β => ⟨fun h => by_contra fun hn => h (hs β fun mu e => hn ⟨mu, e⟩), ?_⟩⟩
  rintro ⟨mu, rfl⟩ h
  exact hσ ((zero_add_nsmul_iff hG s α mu).1 h)

end GlobalTheory.FamFree

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

end GlobalTheory

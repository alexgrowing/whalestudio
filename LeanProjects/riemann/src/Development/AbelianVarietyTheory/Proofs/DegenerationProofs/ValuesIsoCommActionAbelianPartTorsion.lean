import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.ActPt

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem equiv_parts {k : ℕ} {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') :
    ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g.b = p.g.b * DegPre.cF D F z := by
  obtain ⟨z, h₁, g, h₂, h₃⟩ := h
  exact ⟨z, h₁, by rw [h₃.1, h₂.1]; rfl⟩

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)

theorem mul_cF_act (x : O) (b : TF (R := R) F ⟶ D.P.A) (z : D.X) :
    (b * DegPre.cF D F z) ≫ oa.onB.act x = (b ≫ oa.onB.act x) * DegPre.cF D F (x • z) := by
  have := oa.onB.hom x
  rw [MonObj.mul_comp, DegPre.cF, DegPre.cF, oa.c_lin, Category.assoc]

theorem act_parts {k : ℕ} {x : O} {p p' : QkPt D F k} (h : QkAct oa x p p') :
    ∃ z : D.X, p'.y = x • p.y + k • z ∧ p'.g.b = (p.g.b ≫ oa.onB.act x) * DegPre.cF D F z := by
  obtain ⟨q, h₁, h₂, h₃⟩ := h
  obtain ⟨z, e₁, e₂⟩ := equiv_parts h₃
  exact ⟨z, by rw [e₁, h₁], by rw [e₂, h₂.1]⟩
end

theorem exists_image {C : Type} [CommRing C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, (TateInh.homOfIso J).Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  have e := hp k
  rw [N.mem_QT.1 p.2] at e
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), (h₁ _).unique e (h₃ _)⟩, rfl, hg⟩

theorem main : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  intro hL hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT k hk hlab hlin x y y' hy hy'
  letI := H.starRing
  obtain ⟨-, -, -, -, B⟩ := hB O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨t, t₁, -, t₃, -, t₅, -⟩ := hT C k hk
  have im : ∀ w : D.La, ∃ p' : QkPt M.P.D.toPre C k, (t p').left = (o.I.ev k w).left ≫ M.φ ∧
      p'.y = ν'.eX (J.e (A.q k w).1.1.toAdd) ∧ p'.g.b = ν'.eA (J.φ (A.q k w).1.2.b) := fun w => by
    obtain ⟨p, hp, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k w)
    obtain ⟨q, q₁, q₂⟩ := exists_image J p
    obtain ⟨p', hp'⟩ := (B' k).2.1 q
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev k w).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (t₁ _ _).1 (hlab w p q p' z hp q₁ q₂ hp' rfl)
    refine ⟨p', by rw [← hz]; rfl, ?_, ?_⟩
    · rw [← hp'.1, q₁, hp.1]; rfl
    · rw [← hp'.2.1, q₂.1]; exact congrArg (fun s => ν'.eA (J.φ s)) hp.2.1
  obtain ⟨gm, hγ, hγ'⟩ := QStr.root_over A.N hk.ne' 1 y hy
  obtain ⟨p₀, hp₀⟩ := (B k).2.1 ⟨(1, gm), hγ'.trans A.N.io_zero.symm⟩
  obtain ⟨v, hv⟩ := A.I.onto k hk p₀
  obtain ⟨z₀, -, e₀⟩ := equiv_parts hv
  obtain ⟨z₁, d₁, e₁⟩ := act_parts a.oa (A.I.lin k hk x v)
  obtain ⟨p₁, a₁, b₁, c₁⟩ := im v
  obtain ⟨p₂, a₂, b₂, c₂⟩ := im (x • v)
  obtain ⟨p₃, h₃⟩ := qkAct_exists hL.1.globalFns M.P.D.tau_bimult M.P.oD x p₁
  have e₃ : t p₃ = t p₂ := by
    rw [t₅ _ _ _ h₃]
    ext1
    rw [a₂, o.I.lin, Over.comp_left, Over.comp_left, a₁, Category.assoc, Category.assoc, M.act]
  have h₂ : QkAct M.P.oD x p₁ p₂ :=
    (TorusExt.qkAct_iff_of_equiv M.P.D.tau_bimult hL.1.globalFns M.P.oD (qk_equiv_refl M.P.D.tau_bimult p₁) h₃).2
      ((t₃ _ _).1 e₃)
  obtain ⟨z₂, d₂, e₂⟩ := act_parts M.P.oD h₂
  obtain ⟨w₀, rfl⟩ := A.ν.eX.surjective z₀
  obtain ⟨w₁, rfl⟩ := A.ν.eX.surjective z₁
  rw [← (A.hq k v).1, ← (A.hq k (x • v)).1] at d₁
  rw [← (A.hq k v).2.1, ← (A.hq k (x • v)).2.1] at e₁
  rw [← (A.hq k v).2.1, ← hp₀.2.1] at e₀
  rw [b₁, b₂] at d₂
  rw [c₁, c₂] at e₂
  generalize (A.q k v).1.1.toAdd = s₁ at d₁ d₂
  generalize (A.q k (x • v)).1.1.toAdd = s₂ at d₁ d₂
  generalize (A.q k v).1.2.b = β₁ at e₀ e₁ e₂
  generalize (A.q k (x • v)).1.2.b = β₂ at e₁ e₂
  let e : A.N.X ≃+ N'.X := J.e
  let φ : A.N.A ≃* N'.A := J.φ
  have hc : ∀ χ, N'.c (e χ) = φ (A.N.c χ) := J.c_eq
  let act : A.N.X → A.N.X := fun s => A.ν.eX.symm (x • A.ν.eX s)
  have hl : ∀ s, ν'.eX (e (act s)) = x • ν'.eX (e s) := hlin x
  have ha : ∀ s, A.ν.eX (act s) = x • A.ν.eX s := fun s => A.ν.eX.apply_symm_apply _
  change ν'.eX (e s₂) = x • ν'.eX (e s₁) + k • z₂ at d₂
  change ν'.eA (φ β₂) = ν'.eA (φ β₁) ≫ _ * _ at e₂
  change ν'.eA (φ y') = ν'.eA (φ y) ≫ _
  have g₁ : s₂ = act s₁ + k • w₁ := A.ν.eX.injective (by rw [d₁, map_add, map_nsmul, ha])
  have g₂ : z₂ = ν'.eX (e w₁) := by
    rw [g₁, map_add, map_add, map_nsmul, map_nsmul, hl, add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at d₂
    exact (smul_right_injective _ (Int.natCast_ne_zero.2 hk.ne') d₂).symm
  have g₀ : y = β₁ * A.N.c w₀ := A.ν.eA.injective (by rw [map_mul, A.ν.c_eq, ← e₀, hγ])
  have g₃ : y' * A.N.c w₁ = β₂ * A.N.c (act w₀) := A.ν.eA.injective (by
    rw [map_mul, map_mul, hy', g₀, map_mul, A.ν.c_eq, A.ν.c_eq, A.ν.c_eq, mul_cF_act, e₁, ha, mul_right_comm])
  have g₄ := congrArg (fun s => ν'.eA (φ s)) g₃
  simp only [map_mul, ← hc, ν'.c_eq, hl, e₂, ← g₂] at g₄
  rw [mul_right_comm, mul_left_inj] at g₄
  rw [g₄, g₀, map_mul, map_mul, ← hc, ν'.c_eq, mul_cF_act]

end GlobalTheory.Ex.ActPt
end

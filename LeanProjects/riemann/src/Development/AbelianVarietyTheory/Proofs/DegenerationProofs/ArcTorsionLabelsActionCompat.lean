import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel
open GlobalTheory.TorusExt

theorem b_eq_of_equiv {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {j : ℕ} (hj : 0 < j) {p p' : QkPt D F j}
    (h : QkPt.Equiv D F p p') (hy : p.y = 0) (hy' : p'.y = 0) : p'.g.b = p.g.b := by
  letI := gtGroup D F
  obtain ⟨z, h₁, h₂⟩ := (equiv_iff hB _ _).1 h
  rw [hy, hy', zero_add] at h₁
  have hz : z = 0 := by
    have : (j : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h₁.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hj.ne')
  rw [h₂, hz, map_zero, add_zero]

theorem act_compat_on_torsion : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  intro hL hBr E _ _ _ H D R _ _ C _ _ _ A o M hT N' ν' k β u r J j hj hr hlab x b hb
  letI := H.starRing
  have hG := hL.globalFns
  have hB := A.bimult
  have hB' : M.P.D.toPre.TauBimult := M.P.D.tau_bimult
  obtain ⟨-, -, -, -, br⟩ := hBr R A.D₀ A.even A.bimult C A.N A.ν
  obtain ⟨-, -, -, -, br'⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even hB' C N' ν'
  obtain ⟨e1, -, e3⟩ := br j
  obtain ⟨-, e2', e3'⟩ := br' j
  obtain ⟨τ, hτ, hQ, -⟩ := (twJ_mulEquiv C A.N N' k β u J).1 r j hr
  obtain ⟨f, f1, -, f3, -, f5, -⟩ := hT C j hj

  have key : ∀ (v : D.La) (p : QkPt A.D₀ C j), QkPt.Equiv A.D₀ C (A.I.ev j v) p → p.y = 0 →
      ∃ p' : QkPt M.P.D.toPre C j, p'.y = 0 ∧ p'.g.b = ν'.eA (J.φ (A.ν.eA.symm p.g.b)) ∧
        (f p').left = (o.I.ev j v).left ≫ M.φ := by
    intro v p hp hy
    obtain ⟨q, hq, -⟩ := e1 p
    obtain ⟨p', hp'⟩ := e2' (τ q)
    obtain ⟨pv, hpv⟩ := e2' (τ (A.q j v))
    have hE : QkPt.Equiv _ C pv p' := (e3' _ _ _ _ hpv hp').2 ((hQ _ _).1 ((e3 _ _ _ _ (A.hq j v) hq).1 hp))
    obtain ⟨t, t1, t2, t3⟩ := (hτ q _).1 rfl
    obtain ⟨s, s1, s2, s3⟩ := (hτ (A.q j v) _).1 rfl
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev j v).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (f1 _ _).1 (hlab v s _ pv z s1 s2 s3 hpv rfl)
    refine ⟨p', ?_, ?_, ?_⟩
    · have h0 : q.1.1.toAdd = 0 := A.ν.eX.injective (hq.1.trans (hy.trans (map_zero _).symm))
      rw [← hp'.1, t2, t1.1]
      erw [h0, map_zero, map_zero]
    · rw [← hp'.2.1, t3.1, t1.2.1, ← hq.2.1, MulEquiv.symm_apply_apply]
    · rw [← (f3 _ _).2 hE, ← hz]
      rfl
  obtain ⟨p₀, y₀, b₀⟩ := exists_qkPt_of_torsion (F := C) hB hj.ne' (b := A.ν.eA b) (by rw [← map_pow, hb, map_one])
  obtain ⟨v, hv⟩ := A.I.onto j hj p₀
  have hv₁ : QkPt.Equiv A.D₀ C (A.I.ev j (x • v)) (qkSmul hB hG A.oa x p₀) :=
    (qkAct_iff_of_equiv hB hG A.oa hv (A.I.lin j hj x v)).1 (qkAct_qkSmul hB hG A.oa x p₀)
  obtain ⟨p₀', c₀, d₀, g₀⟩ := key v p₀ hv y₀
  obtain ⟨p₁', c₁, d₁, g₁⟩ := key (x • v) _ hv₁ (by
    change x • p₀.y = 0
    rw [y₀, smul_zero])
  have hf : f (qkSmul hB' hG M.P.oD x p₀') = f p₁' := by
    rw [f5 x _ _ (qkAct_qkSmul hB' hG M.P.oD x p₀')]
    refine Over.OverMorphism.ext ?_
    rw [g₁, Over.comp_left, g₀, o.I.lin, Over.comp_left, Category.assoc, Category.assoc, M.act]
  have hb' := b_eq_of_equiv hB' hj ((f3 _ _).1 hf) (by
    change x • p₀'.y = 0
    rw [c₀, smul_zero]) c₁
  have a₁ : (qkSmul hB' hG M.P.oD x p₀').g.b = p₀'.g.b ≫ M.P.oD.onB.act x := gtSmul_b hG M.P.oD x _
  have a₀ : (qkSmul hB hG A.oa x p₀).g.b = p₀.g.b ≫ A.oa.onB.act x := gtSmul_b hG A.oa x _
  rw [d₁, a₁, a₀, d₀, b₀, MulEquiv.symm_apply_apply] at hb'
  unfold actV
  rw [← hb', MulEquiv.symm_apply_apply]

end GlobalTheory.Relabel

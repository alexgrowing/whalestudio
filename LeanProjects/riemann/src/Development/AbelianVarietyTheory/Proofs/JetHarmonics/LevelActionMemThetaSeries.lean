import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaLevelMove

section Move

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.TranslMove GlobalTheory.VVRank GlobalTheory.ShortValMove
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_isVtOver {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {L₀ : RigLB G} {L₁ : RigLB A}
    {w : LB.Iso L₁.L (L₀.L.pull φ)} (hw : w.IsGen)
    {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left} (he : eSec A ≫ φ = e ≫ eSec G)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) L₁.rig L₀.rig e) (N : ℕ)
    (hk : ∀ θ : ThetaGrp A L₁.L ((N : ℤ) ^ 2) T, θ.pt ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow G L₀.L 1 T₀)} {s : LB.Sec (LPow A L₁.L 1 T)} (hs : SecRel w Ψ s₀ s)
    {ok₀ : (T₀ ⟶ G) → Prop} {ok : (T ⟶ A) → Prop} {t₀ : T₀ ⟶ G} {t : T ⟶ A}
    (ht : ∀ y : T₀ ⟶ G, y ^ N = t₀ → ok₀ y → ∃ x : T ⟶ A, τ ≫ y.left = x.left ≫ φ ∧ x ^ N = t ∧ ok x)
    {F₀ : LB.Sec (LPow G L₀.L ((N : ℤ) ^ 2) T₀)} (H : IsVtOver G L₀ N ok₀ s₀ t₀ F₀) :
    ∃ F, IsVtOver A L₁ N ok s t F ∧ SecRel w Ψ F₀ F := by
  obtain ⟨y₁, β₀, β, r₁, V₁, hy, oy, g₀, n₀, cβ, tw, sl₁, ac₁⟩ := H
  obtain ⟨x₁, hx₁, hx, ox⟩ := ht y₁ hy oy
  obtain ⟨α₀, gα₀, nα₀, v₀⟩ := exists_normMul hp L₀.isLB L₁.isLB hw he hρ N g₀ n₀
  obtain ⟨α, gα, cα⟩ := NormMulUniv.exists_pull L₁.isLB α₀ gα₀ T
  have v : GenRel w Ψ β α := fun Z r z J₀ J hJ₀ hJ => by
    rw [val_corr hJ₀ cβ, val_pull hJ₀, val_corr hJ cα, val_pull hJ, Category.assoc, h₂, ← Category.assoc,
      v₀ Z _ z J₀ J hJ₀ hJ, Category.comp_id, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨s₁, tw'⟩ := VVRank.exists_isTwistPull A (ψ := mulT A T N) (hm := lift_snd _ _) (b := 1) L₁.isLB gα s
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow hp h₂ N) h₂) v tw tw' hs
  obtain ⟨U₁, l₁, a₁⟩ := exists_symLift hp L₀.isLB L₁.isLB hw h₁ h₂ hk hx₁ sl₁
  obtain ⟨F, b₁, R₂⟩ := a₁ _ _ _ ac₁ R₁
  exact ⟨F, ⟨x₁, α₀, α, s₁, U₁, hx, ox, gα₀, nα₀, cα, tw', l₁, b₁⟩, R₂⟩

theorem isVtOver_move (hLaw : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {x x' : Sp S ⟶ Xo.X} {pm : Gx x ⟶ Gx x'}
    {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)}
    (h₁ : pm ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) (hw : CubIso ν w)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (hs : SecRel (T := Over.mk x) (T₀ := Over.mk x') w pm s' s) (N : ℕ)
    {ok' : (ptO Xo x' ⟶ Xo.univ.t.G) → Prop} {ok : (ptO Xo x ⟶ Xo.univ.t.G) → Prop}
    {t' : ptO Xo x' ⟶ Xo.univ.t.G} {t : ptO Xo x ⟶ Xo.univ.t.G}
    (ht : ∀ q : ptO Xo x' ⟶ Xo.univ.t.G, q ^ N = t' → ok' q →
      ∃ p : ptO Xo x ⟶ Xo.univ.t.G, q.left = p.left ≫ ν.φ ∧ p ^ N = t ∧ ok p)
    {F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x'))}
    (hF : IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok' s' t' F') :
    ∃ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x)),
      IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F ∧ SecRel (T := ptO Xo x) (T₀ := ptO Xo x') w pm F' F := by
  have := UnivPol.isLocallyNoetherian Xo
  have hρ := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig Xo.univ.t.PP.rig ν.cm.e _
    (rigPull_le ν.cm.F ν.cm.e ν.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw.2.1
  exact exists_isVtOver ν.cart (T := ptO Xo x) (T₀ := ptO Xo x') (τ := 𝟙 (Sp S)) hw.1
    (h₁.trans (Category.comp_id _).symm) h₂ ν.cm.e_comm hρ N
    (fun θ => pt_pow_eq_one hLaw.kerPow (UnivPol.pol Xo) (N ^ 2) (Nat.cast_pow N 2).symm θ) hs
    (fun q hq oq => (ht q hq oq).imp fun p hp => ⟨(Category.id_comp _).trans hp.1, hp.2⟩) hF

theorem nab_move (hLaw : Laws) (hCI : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c}
    (hnab : IsNab Xo c nab) {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} {pm : Gx y.x ⟶ Gx y'.x}
    {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (hx : y'.x = y.x ≫ ρ)
    (h₁ : pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left)
    (h₂ : pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ) (hw : CubIso ν w)
    (hu : ∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)))
    (hF : ∀ b, SecRel (T := ptO Xo y.x) (T₀ := ptO Xo y'.x) w pm (F' b) (F b)) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  have hL := Xo.univ.t.PP.isLB
  have e : (N : ℤ) ^ 2 = (N ^ 2 : ℕ) := (Nat.cast_pow N 2).symm
  refine GlobalTheory.T.harmonic_values_invariant_universal_endomorphism hLaw hCI E H Dw l Xo c nab hnab S ρ ν y y' pm w hx h₁ h₂ hw hu n a P hP N F F' fun b => ?_
  have hc := @secRel_iff _ _ _ _ _ _ ν.cm.F (ptO Xo y.x) (ptO Xo y'.x) _ _ w pm hL hL h₂ ((N : ℤ) ^ 2) (N ^ 2) e
  exact (hc _ _).1 (hF b)

theorem thValAt_move (hLaw : Laws) (hCI : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c}
    (hnab : IsNab Xo c nab) {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c S}
    (hlev : IsLevMove ρ ν gM gA) (hmv : FrMove ρ ν y y') {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {x : Fin n → Dw.La} {v : S} (hv : ThValAt Xo c nab y' x P v) :
    ThValAt Xo c nab y (fun b => gM (x b)) P v := by
  obtain ⟨S', _, _, φ, y₁', F', hff, hfr, hV, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : Dw.La, e (levPt Xo y₁.x (gM q)) = levPt Xo y₁'.x q := fun q => by
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun b : Fin n =>
    isVtOver_move hLaw hf hs hω hR l.M (ok := KilledBy Xo (l.Mb ^ 2)) (t := levPt Xo y₁.x (gM (x b)))
      (fun p hp op => ⟨e.symm p, he' p, by rw [← map_pow, hp, ← hlv, e.symm_apply_apply],
        fun r hr => by rw [hact', op r hr, map_one]⟩) (hV b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, F, hff, hy₁, hF, ?_⟩
  rw [hval, thExpr, thExpr, nab_move hLaw hCI hnab hx hf hs hω hu hP l.M F F' hFF]

end Move

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem actLev_mem_th : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  intro hCI D T h j hj w γ f hf _
  obtain ⟨x, P, hP, hf⟩ := hf
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
    have hk := D.R.m_add_three_le_k
    have h1 := hj.1
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have hA := (GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hr h.pins.2.1.2).total
  refine ⟨fun b => liftLa γ (x b), P, hP, fun p y => ?_⟩
  obtain ⟨ρ, ν, -, hlev, hmv⟩ := mvPt_spec hA γ y
  exact thValAt_move GlobalTheory.firstFiveLaws.1 hCI hnab hlev hmv hP.1 (hf p _)

end GlobalTheory.ThetaLevelMove

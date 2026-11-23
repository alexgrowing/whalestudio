import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Norm

section General

variable {X X' S : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_iso (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (e : S ⟶ X) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
        e' (r z) ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j → e' (r z) ∈ L'.U q →
        gv w (r ≫ e') z j q = gm ((r ≫ e') ≫ Φ) z (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) *
          (gm r z (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹ := by
  have hw := (isGen_iff w₀).1 hw₀
  obtain ⟨u, hu, vu⟩ := exists_up hw hL hL' (K := PUnit) (φ' := fun _ => e') (ε := fun _ => 1) ρ' hρ'
  have l₀ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      (L.pull Φ).U (fun _ => j 0) ⊓ L'.U q := fun j q x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx.1 0), hx.2⟩
  have l₁ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 1
  have l₂ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 2
  let w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε) :=
    ⟨fun c => res (l₀ c.1 c.2) (w₀.s (fun _ => c.1 0, c.2)) *
      (res (l₁ c.1 c.2) (pullU p _ (u.s (fun _ => c.1 1))))⁻¹ * res (l₂ c.1 c.2) (pullU p _ (ρ.s (fun _ => c.1 2)))⟩
  have vw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X') (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
      f z ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q →
      gm f z (LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q) (w.s (j, q)) = gw w₀ f z (j 0) q *
        (gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1)) (u.s (fun _ => j 1)))⁻¹ *
        gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) := fun Z f z j q hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₀ j q) hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ j q) hz _).trans (gm_pull f p z _ (l₁ j q hz) _))))))
      ((gm_res f z (l₂ j q) hz _).trans (gm_pull f p z _ (l₂ j q hz) _)))
  refine ⟨w, ?_, fun Z r z j q hj hq => ?_⟩
  · rintro ⟨j, q⟩ ⟨j', q'⟩
    refine unit_ext fun x hx => ?_
    refine ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j q hx.1)).trans (Eq.symm ((map_mul _ _ _).trans
      ((congrArg₂ (· * ·) ((gm_div L' _ (𝟙 X') x (j, q) (j', q') hx).trans
        (congrArg (· * _) (gm_linComb L _ twε (𝟙 X') x j j' hx.1.1 hx.2.1)))
        ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j' q' hx.2))).trans ?_)))
    rw [hw _ (𝟙 X') x (j 0) (j' 0) q q' (Set.mem_iInter.1 hx.1.1 0) (Set.mem_iInter.1 hx.2.1 0) hx.1.2 hx.2.2,
      gen_trans hu (𝟙 X' ≫ p) x (l₁ j q hx.1) (l₁ j' q' hx.2), gen_trans hρ (𝟙 X' ≫ p) x (l₂ j q hx.1) (l₂ j' q' hx.2),
      Fin.prod_univ_three]
    simp only [trF, Fintype.prod_unique, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_one,
      zpow_neg, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
    have hz : p (e' (r z)) = r z := congrArg (fun g => g z) hp
    have m₀ : Φ (e' (r z)) ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have m₁ : Φ (e' (r z)) ∈ L.U (j 1) := by
      have : Φ (e' (p (e' (r z)))) ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
      rwa [hz] at this
    refine (vw Z (r ≫ e') z j q ⟨hj, hq⟩).trans ?_
    rw [hp, vu Z r z (fun _ => j 1) (fun _ => q) (Set.mem_iInter.2 fun _ => m₁) (Set.mem_iInter.2 fun _ => hq),
      pw, Fintype.prod_unique, zpow_one, hw Z (r ≫ e') z (j 0) (j 1) q q m₀ m₁ hq hq, gm_self hL' (r ≫ e') z hq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, inv_one, ofMul_one]
    abel

theorem exists_iso_maps (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (b e : S ⟶ X) (hb : e' ≫ Φ = b) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) {Y : Scheme.{0}} (r : Y ⟶ S) (x : Y ⟶ X') (hx : x = r ≫ e')
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x) (fun _ => -1)))
    (ha : ∀ (y : Y) (q : L'.ι), e' (r y) ∈ L'.U q →
      gm (𝟙 Y) y (LB.wchart L' (fun _ : PUnit => x) (fun _ => q)) (a.s (fun _ => q)) =
        (gm r y (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ b, p ≫ e] twε), w.IsGen ∧
      ∃ t : LB.Gen (LB.LinComb L (fun i => x ≫ (![Φ, p ≫ b, p ≫ e] : Fin 3 → (X' ⟶ X)) i) (fun i => -1 * twε i)),
        MapsAtExp L L' ![Φ, p ≫ b, p ≫ e] twε w x (-1) a t ∧
        ∀ y J, Good L y J → val t (𝟙 Y) y J = (val ρ r y J)⁻¹ := by
  subst hb hx
  obtain ⟨w, hw, vw⟩ := exists_iso hL hL' p e' he Φ e ρ' hρ' ρ hρ w₀ hw₀
  have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
  have hz : ∀ z, p (e' (r z)) = r z := fun z => congrArg (fun g => g z) hp
  have l₁ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        ((r ≫ e') ≫ Φ) ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, by
    have : Φ (e' (p (e' (r y)))) ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    rw [hz] at this
    exact this⟩
  have l₂ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        r ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j y hy => Set.mem_iInter.2 fun _ => by
    have : e (p (e' (r y))) ∈ L.U (j 2) := Set.mem_iInter.1 hy 2
    rw [hz] at this
    exact this
  let t : LB.Gen (LB.LinComb L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i)
      (fun i => -1 * twε i)) :=
    ⟨fun j => (res (l₁ j) (pullU ((r ≫ e') ≫ Φ) (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1))) * res (l₂ j) (pullU r _ (ρ.s (fun _ => j 2))))⁻¹⟩
  have vt : ∀ (y : Y) (j : Fin 3 → L.ι),
      y ∈ LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j →
      gm (𝟙 Y) y (LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j) (t.s j) =
        (gm ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r y (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)))⁻¹ := fun y j hy =>
    (map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 Y) y (l₁ j) hy _).trans ((gm_pull (𝟙 Y) ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (l₁ j hy) _).trans (by rw [Category.id_comp])))
      ((gm_res (𝟙 Y) y (l₂ j) hy _).trans ((gm_pull (𝟙 Y) r y _ (l₂ j hy) _).trans (by rw [Category.id_comp]))))))
  refine ⟨w, hw, t, fun j q => unit_ext fun y hy => ?_, fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 Y) y _ hy _).trans (vt y j (mapsAtExp_le_b L L' _ twε _ j q hy))).trans
      (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ))
        ((gm_pull (𝟙 Y) (r ≫ e') y _ hy _).trans ((congrArg (fun f => gv w f y j q) (Category.id_comp _)).trans
          (vw Y r y j q hy.1 hy.2))))) ((gm_res (𝟙 Y) y _ hy _).trans (ha y q hy.2))).trans ?_)))
    rw [zpow_neg, zpow_one, ← mul_inv, inv_mul_cancel_right]
  · have e₁ : (r ≫ e') ≫ p ≫ e' ≫ Φ = (r ≫ e') ≫ Φ := by rw [← Category.assoc, hp, Category.assoc]
    have e₂ : (r ≫ e') ≫ p ≫ e = r ≫ e := by rw [← Category.assoc, hp]
    rw [val_of t (𝟙 Y) y J ![J ((r ≫ e') ≫ Φ), J ((r ≫ e') ≫ Φ), J (r ≫ e)] (fun k => by
      rw [Category.id_comp]
      fin_cases k
      exacts [rfl, congrArg J e₁, congrArg J e₂])]
    refine (vt y _ (Set.mem_iInter.2 fun k => ?_)).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ e') ≫ Φ)
      · show ((r ≫ e') ≫ p ≫ e' ≫ Φ) y ∈ L.U (J ((r ≫ e') ≫ Φ))
        rw [e₁]; exact hJ _
      · show ((r ≫ e') ≫ p ≫ e) y ∈ L.U (J (r ≫ e))
        rw [e₂]; exact hJ _
    · exact congrArg (·⁻¹) ((congrArg (· * _) (gm_self hL ((r ≫ e') ≫ Φ) y (hJ _))).trans (_root_.one_mul _))

end General

theorem exists_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A), IsMonHom β → ∀ w₀ : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left), w₀.IsGen → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  intro R _ _ I D D₂ g β hβ w₀ hw₀
  have hb : eSec D₂.toPre.P.A ≫ (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left = g.b.left := by
    rw [eSec, ← Over.comp_left]
    congr 1
    show η[D₂.toPre.P.A] ≫ (β * (toUnit D₂.toPre.P.A ≫ g.b)) = g.b
    have h₁ : η[D₂.toPre.P.A] ≫ β = 1 := by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have h₂ : η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A = 𝟙 _ := toUnit_unique _ _
    rw [MonObj.comp_mul, h₁, ← Category.assoc, h₂, Category.id_comp, _root_.one_mul]
  have he : eSec D₂.toPre.P.A ≫ (toUnit D₂.toPre.P.A).left = 𝟙 _ := by
    rw [eSec, ← Over.comp_left, toUnit_unique (η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A) (𝟙 _)]
    rfl
  obtain ⟨w, hw, t, h₁, h₂⟩ := exists_iso_maps D.toPre.P.isLB D₂.toPre.P.isLB (toUnit D₂.toPre.P.A).left
    (eSec D₂.toPre.P.A) he _ g.b.left (eSec D.toPre.P.A) hb D₂.toPre.rig D₂.toPre.rig_gen D.toPre.rig D.toPre.rig_gen
    w₀ hw₀ (jK R) (D₂.toPre.xK 0) (Uniq.xK_zero D₂.toPre) (D₂.toPre.psi 0)
    (fun y q hq => Uniq.gm_psi_zero D₂.tau_bimult 0 rfl y q hq)
  refine ⟨w, hw, t, h₁, corr_of_val D.toPre.P.isLB fun y J hJ => (h₂ y J hJ).trans ?_⟩
  refine Eq.symm ((val_mul hJ _ _ _).trans ?_)
  rw [PsiZero.val_psi_zero D.tau_bimult hJ, val_pull hJ, val_corr hJ g.s_zero, val_one, _root_.mul_one]

end GlobalTheory.MumCmp.Norm

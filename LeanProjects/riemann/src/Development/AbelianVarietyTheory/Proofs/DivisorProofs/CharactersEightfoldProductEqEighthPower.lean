import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchIdOneMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Chars8

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (g : G ⟶ H) [IsMonHom g] {κ : Type} (s : Finset κ) (f : κ → (T ⟶ G)) :
    (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem main : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq huniv
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  choose c hc using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U (q u) (hq u)

  let y : Fin 8 → Fin 8 → (G₀ ⟶ G₀) := fun u v => if v = u then 𝟙 G₀ else 1
  choose sc hsc _ using fun u => huniv G₀ (y u)
  have hscm : ∀ u, IsMonHom (sc u) := fun u => isMonHom_of_mul _ fun T a b => by
    refine (huniv T (fun v => (a * b) ≫ y u v)).unique (fun v => ?_) (fun v => ?_)
    · rw [Category.assoc, hsc]
    · haveI := hq v
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsc]
      by_cases h : v = u
      · simp only [y, h, if_true, Category.comp_id]
      · simp only [y, h, if_false, comp_one, _root_.mul_one]
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G hG D P U G₀ hG₀ D₀ A₀ U₀ (sc u) (hscm u)
  obtain ⟨hid₀, hone₀, -⟩ := torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G₀ hG₀ D₀ A₀ U₀
  obtain ⟨hid, hone, hmul⟩ := torMatch_id_one_mul V₁ hB G hG D P U G hG D P U

  have dc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h := torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q v).left V₁ hB G₀ hG₀ D₀ A₀ U₀
      (RingHom.id V₁) (sc u).left Function.injective_id (fun k hk => hk) (c v) (d u) (hc v) (hd u)
    rw [RingHom.id_comp, ← Over.comp_left, hsc] at h
    by_cases huv : v = u
    · simp only [y, huv, if_true, Over.id_left] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hid₀
    · simp only [y, huv, if_false] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hone₀
  have dsum : ∀ (χ : Fin 8 → D₀.toPre.X) w, d w (∑ u, c u (χ u)) = χ w := by
    intro χ w
    rw [map_sum, Finset.sum_eq_single w]
    · have := DFunLike.congr_fun (dc w w) (χ w)
      simpa using this
    · intro b _ hb
      have := DFunLike.congr_fun (dc w b) (χ b)
      simpa [hb] using this
    · intro h; exact absurd (Finset.mem_univ w) h

  have hprod : (∏ v, q v ≫ sc v) = 𝟙 G := by
    refine (huniv G q).unique (fun w => ?_) (fun w => Category.id_comp _)
    haveI := hq w
    rw [prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hsc]; simp only [y, if_true, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, hsc]
      simp only [y, Ne.symm hb, if_false, comp_one]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hs : ∀ s : Finset (Fin 8), TorMatch U U (RingHom.id V₁) (∏ v ∈ s, q v ≫ sc v).left
      (∑ v ∈ s, (c v).comp (d v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hmul _ _ _ _ ?_ ih
      have h := torMatch_comp V₁ hB G hG D P U V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) (sc a).left V₁ hB G hG D P U
        (RingHom.id V₁) (q a).left Function.injective_id (fun k hk => hk) (d a) (c a) (hd a) (hc a)
      rwa [RingHom.id_comp, ← Over.comp_left] at h
  have hsum : (∑ v, (c v).comp (d v)) = AddMonoidHom.id _ := by
    have h := hs Finset.univ
    rw [hprod, Over.id_left] at h
    exact torMatch_unique V₁ hB G hG D P U V₁ hB G hG D P U (RingHom.id V₁) _ Function.injective_id _ _ h hid
  refine ⟨c, hc, fun χ χ' h => funext fun w => ?_, fun z => ⟨fun v => d v z, ?_⟩⟩
  · rw [← dsum χ w, ← dsum χ' w]; exact congrArg (d w) h
  · have := DFunLike.congr_fun hsum z
    rw [AddMonoidHom.finset_sum_apply] at this
    simpa using this

end GlobalTheory.Poinc.Eq8.Chars8

end

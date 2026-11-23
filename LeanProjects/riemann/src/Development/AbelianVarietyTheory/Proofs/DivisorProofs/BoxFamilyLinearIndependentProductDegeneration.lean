import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxFamLinearIndependent

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdIndep

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.BoxFamIndep

theorem tensor_indep (F O₁ O₂ : Type) [Field F] [CommRing O₁] [Algebra F O₁] [CommRing O₂] [Algebra F O₂]
    {A₁ A₂ : Type} {m n : ℕ} (β₁ : A₁ → Fin m → O₁) (β₂ : A₂ → Fin n → O₂)
    (h₁ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β₁ α l = 0) → c = 0)
    (h₂ : ∀ c : Fin n → F, (∀ α, ∑ l, c l • β₂ α l = 0) → c = 0) (c : Fin m × Fin n → F)
    (hc : ∀ α₁ α₂, ∑ a, c a • (β₁ α₁ a.1 ⊗ₜ[F] β₂ α₂ a.2) = 0) : c = 0 := by
  have key : ∀ α₁ α₂, ∑ l : Fin m, β₁ α₁ l ⊗ₜ[F] (∑ a : Fin n, c (l, a) • β₂ α₂ a) = 0 := by
    intro α₁ α₂
    rw [← hc α₁ α₂, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => TensorProduct.tmul_smul _ _ _
  have key2 : ∀ l, (fun a : Fin n => c (l, a)) = 0 := fun l => h₂ _ fun α => by
    refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
    refine congrFun (h₁ (fun l => φ (∑ a : Fin n, c (l, a) • β₂ α a)) fun α₀ => ?_) l
    have := congrArg (fun t => TensorProduct.rid F O₁ (LinearMap.lTensor O₁ φ t)) (key α₀ α)
    simpa only [map_sum (LinearMap.lTensor O₁ φ), map_sum (TensorProduct.rid F O₁), LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_zero] using this
  funext a
  exact congrFun (key2 a.1) a.2

theorem exists_test₂ {F : Type} [Field F] {X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of F))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of F)) (x₁ : X₁) (x₂ : X₂) {A₁ A₂ : Type} {U₁ : A₁ → X₁.Opens}
    {U₂ : A₂ → X₂.Opens} (hx₁ : ∀ α, x₁ ∈ U₁ α) (hx₂ : ∀ α, x₂ ∈ U₂ α) {m n : ℕ}
    (s₁ : ∀ α, Fin m → Γ(X₁, U₁ α)) (s₂ : ∀ α, Fin n → Γ(X₂, U₂ α))
    (hs₁ : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p₁ x₁ (c l) * gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l) = 0) → c = 0)
    (hs₂ : ∀ c : Fin n → F, (∀ α, ∑ l, germOf p₂ x₂ (c l) * gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l) = 0) → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂), r₁ ≫ p₁ = q ∧ r₂ ≫ p₂ = q ∧
      (∀ z α, r₁ z ∈ U₁ α) ∧ (∀ z α, r₂ z ∈ U₂ α) ∧ ∀ c : Fin m × Fin n → F,
        (∀ α₁ α₂ z, ∑ a, germOf q z (c a) * (gs r₁ z (U₁ α₁) (s₁ α₁ a.1) * gs r₂ z (U₂ α₂) (s₂ α₂ a.2)) = 0) →
          c = 0 := by
  let : Algebra F (X₁.presheaf.stalk x₁) := (germOf p₁ x₁).toAlgebra
  let : Algebra F (X₂.presheaf.stalk x₂) := (germOf p₂ x₂).toAlgebra
  have h := tensor_indep F _ _ (fun α l => gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l)) (fun α l => gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l))
    (fun c hc => hs₁ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
    (fun c hc => hs₂ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
  obtain ⟨B, _, _, e₁, e₂, h⟩ : ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (e₁ : X₁.presheaf.stalk x₁ →ₐ[F] B)
      (e₂ : X₂.presheaf.stalk x₂ →ₐ[F] B), ∀ c : Fin m × Fin n → F, (∀ α₁ α₂, ∑ a, c a •
        (e₁ (gs (𝟙 X₁) x₁ (U₁ α₁) (s₁ α₁ a.1)) * e₂ (gs (𝟙 X₂) x₂ (U₂ α₂) (s₂ α₂ a.2))) = 0) → c = 0 :=
    ⟨TensorProduct F (X₁.presheaf.stalk x₁) (X₂.presheaf.stalk x₂), inferInstance, inferInstance,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, fun c hc => h c fun α₁ α₂ => by
        rw [← hc α₁ α₂]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]⟩
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    (Spec.map (CommRingCat.ofHom e₁.toRingHom) : _ ⟶ Spec (X₁.presheaf.stalk x₁)) ≫ X₁.fromSpecStalk x₁,
    (Spec.map (CommRingCat.ofHom e₂.toRingHom) : _ ⟶ Spec (X₂.presheaf.stalk x₂)) ≫ X₂.fromSpecStalk x₂,
    ?_, ?_, fun z α => fromSpecStalk_mem x₁ (hx₁ α) _, fun z α => fromSpecStalk_mem x₂ (hx₂ α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₁.commutes a
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₂.commutes a
  · refine h c fun α₁ α₂ => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    rw [← hc α₁ α₂ z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · rw [gs_fromSpecStalk x₁ (hx₁ _)]
      exact (germOf_map (B := X₁.presheaf.stalk x₁) (𝟙 _) (CommRingCat.ofHom e₁.toRingHom) z _).symm
    · rw [gs_fromSpecStalk x₂ (hx₂ _)]
      exact (germOf_map (B := X₂.presheaf.stalk x₂) (𝟙 _) (CommRingCat.ofHom e₂.toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem exists_pt {D : DegPre R} {m : ℕ} (b : Fin m → Fam D F k) (hb : LinearIndependent F b) :
    ∃ (x : (DegPre.BF D F).left) (jj : D.X → Fin 4 → D.P.L.ι),
      (∀ α, x ∈ LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) ∧ ∀ c : Fin m → F,
      (∀ α, ∑ l, germOf (B := CommRingCat.of F) (fst (TF (R := R) F) D.P.A).left x (c l) *
        gs (𝟙 _) x (LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) (((b l).s α).f (jj α)) = 0) → c = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  refine ⟨_, _, hx, fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => ?_⟩
  refine fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
  refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
  rw [Category.id_comp]
  exact hc α

theorem exists_pair {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) [IsIso (lift p₁ p₂)]
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ (DegPre.BF D₁ F).left)
    (r₂ : Z ⟶ (DegPre.BF D₂ F).left) (h₁ : r₁ ≫ (fst (TF (R := R) F) D₁.P.A).left = q)
    (h₂ : r₂ ≫ (fst (TF (R := R) F) D₂.P.A).left = q) :
    ∃ ρ : Z ⟶ (DegPre.BF D F).left, ρ ≫ (TF (R := R) F ◁ p₁).left = r₁ ∧ ρ ≫ (TF (R := R) F ◁ p₂).left = r₂ ∧
      ρ ≫ (fst (TF (R := R) F) D.P.A).left = q := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r₁' : T ⟶ DegPre.BF D₁ F := Over.homMk r₁ (by
    rw [← Over.w (fst (TF (R := R) F) D₁.P.A), ← Category.assoc, h₁]; rfl)
  let r₂' : T ⟶ DegPre.BF D₂ F := Over.homMk r₂ (by
    rw [← Over.w (fst (TF (R := R) F) D₂.P.A), ← Category.assoc, h₂]; rfl)
  let ρ : T ⟶ DegPre.BF D F := lift q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _))
  have hρ₁ : ρ ≫ TF (R := R) F ◁ p₁ = r₁' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₁.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_fst _ _ _ _
  have hρ₂ : ρ ≫ TF (R := R) F ◁ p₂ = r₂' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₂.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_snd _ _ _ _
  exact ⟨ρ.left, congrArg (fun g => g.left) hρ₁, congrArg (fun g => g.left) hρ₂,
    congrArg (fun g => g.left) (lift_fst q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _)))⟩

theorem boxFam₂_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w F _ _ k m n b₁ b₂ b hb₁ hb₂ hb
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := hS.lim
  obtain ⟨x₁, j₁, hx₁, H₁⟩ := exists_pt b₁ hb₁
  obtain ⟨x₂, j₂, hx₂, H₂⟩ := exists_pt b₂ hb₂
  obtain ⟨Z, q, r₁, r₂, hq₁, hq₂, hr₁, hr₂, H⟩ := exists_test₂ (F := F) (fst (TF (R := R) F) D₁.P.A).left
    (fst (TF (R := R) F) D₂.P.A).left x₁ x₂ hx₁ hx₂ (fun α l => ((b₁ l).s α).f (j₁ α))
    (fun α l => ((b₂ l).s α).f (j₂ α)) H₁ H₂
  obtain ⟨ρ, hρ₁, hρ₂, hρq⟩ := exists_pair p₁ p₂ q r₁ r₂ hq₁ hq₂
  refine H c fun α₁ α₂ z => ?_
  obtain ⟨α, rfl, rfl⟩ : ∃ α, q₁ α = α₁ ∧ q₂ α = α₂ := by
    obtain ⟨α, h⟩ := hS.xsum.2 (α₁, α₂)
    exact ⟨α, congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB z
  have hm := hJ.mem (DegPre.famφ D F α) ρ
  have E := (gs_comb c b α _ ρ z hm).symm.trans
    ((congrArg (fun s : Fam D F k => gs (Y := Z) ρ z _ ((s.s α).f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => hb a α Z ρ z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [hρ₁, hρ₂] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b a).s α) ρ z J =
      sval ((b₁ a.1).s (q₁ α)) r₁ z J₁ * sval ((b₂ a.2).s (q₂ α)) r₂ z J₂ := ⟨_, E'⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₁ z (LB.wchart D₁.P.L (DegPre.famφ D₁ F (q₁ α)) (j₁ (q₁ α))) (((b₁ l).s (q₁ α)).f (j₁ (q₁ α))) =
      v * sval ((b₁ l).s (q₁ α)) r₁ z J₁ :=
    ⟨_, fun l => sec_trans _ r₁ z (hr₁ z _) (hJ₁.mem _ r₁)⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₂ z (LB.wchart D₂.P.L (DegPre.famφ D₂ F (q₂ α)) (j₂ (q₂ α))) (((b₂ l).s (q₂ α)).f (j₂ (q₂ α))) =
      v * sval ((b₂ l).s (q₂ α)) r₂ z J₂ :=
    ⟨_, fun l => sec_trans _ r₂ z (hr₂ z _) (hJ₂.mem _ r₂)⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((v₁ * v₂) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((congrArg₂ (· * ·) (hv₁ a.1) (hv₂ a.2)).trans (_root_.mul_mul_mul_comm _ _ _ _)).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end GlobalTheory.ProdIndep

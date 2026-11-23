import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPB_of_zRel_actPB : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B)
    (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A))
    (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)),
    ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hZ₁ hZ₂
  obtain ⟨ψ, ψ₂, hψ, sψ, lψ, vψ, aψ⟩ := hA
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, L₁, V₁, -⟩ := hZ₁
  obtain ⟨inc₂, pr₂, mi₂, mp₂, ip₂, pi₂, L₂, V₂, -⟩ := hZ₂
  have ip₁' : inc₁.left ≫ pr₁.left = 𝟙 _ := by rw [← Over.comp_left, ip₁]; rfl
  have ip₂' : inc₂.left ≫ pr₂.left = 𝟙 _ := by rw [← Over.comp_left, ip₂]; rfl
  have pi₁' : pr₁.left ≫ inc₁.left = (act₁ e).left := by rw [← Over.comp_left, pi₁]
  have pi₂' : pr₂.left ≫ inc₂.left = (act₂ e).left := by rw [← Over.comp_left, pi₂]
  have K0 : inc₂.left ≫ (act₂ e).left = inc₂.left := by
    rw [← pi₂', ← Category.assoc, ip₂', Category.id_comp]
  obtain ⟨φ, hφ⟩ : ∃ φ : c₂.A.left ⟶ c₁.A.left, φ = inc₂.left ≫ ψ ≫ pr₁.left := ⟨_, rfl⟩
  have K1 : φ ≫ inc₁.left = inc₂.left ≫ ψ := by
    rw [hφ, Category.assoc, Category.assoc, pi₁', ← aψ e, ← Category.assoc, K0]
  have K2 : pr₂.left ≫ φ = ψ ≫ pr₁.left := by
    have : (act₁ e).left ≫ pr₁.left = pr₁.left := by
      rw [← pi₁', Category.assoc, ip₁', Category.comp_id]
    rw [hφ, ← Category.assoc, ← Category.assoc, pi₂', aψ e, Category.assoc, this]
  have hw : φ ≫ c₁.A.hom = c₂.A.hom ≫ y := by
    rw [hφ, Category.assoc, Category.assoc, Over.w pr₁, hψ.1.w, ← Category.assoc, Over.w inc₂]
  have hpb : IsPullback φ c₂.A.hom c₁.A.hom y := by
    let lft : ∀ s : PullbackCone c₁.A.hom y, s.pt ⟶ c₂.A.left := fun s =>
      hψ.1.lift (s.fst ≫ inc₁.left) s.snd (by rw [Category.assoc, Over.w inc₁]; exact s.condition) ≫ pr₂.left
    refine IsPullback.of_isLimit (c := PullbackCone.mk φ c₂.A.hom hw)
      (PullbackCone.IsLimit.mk hw lft (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
    · simp only [lft]
      rw [Category.assoc, K2, ← Category.assoc, hψ.1.lift_fst, Category.assoc, ip₁', Category.comp_id]
    · simp only [lft]
      rw [Category.assoc, Over.w pr₂, hψ.1.lift_snd]
    · have e₁ : m ≫ inc₂.left = hψ.1.lift (s.fst ≫ inc₁.left) s.snd
          (by rw [Category.assoc, Over.w inc₁]; exact s.condition) := by
        apply hψ.1.hom_ext
        · rw [hψ.1.lift_fst, Category.assoc, ← K1, ← Category.assoc, hm1]
        · rw [hψ.1.lift_snd, Category.assoc, Over.w inc₂, hm2]
      calc m = m ≫ inc₂.left ≫ pr₂.left := by rw [ip₂', Category.comp_id]
        _ = lft s := by rw [← Category.assoc, e₁]
  have hmul : ∀ (T : Over S₂) (x x' : T ⟶ c₂.A) (x₀ x₀' : Over.mk (T.hom ≫ y) ⟶ c₁.A),
      x₀.left = x.left ≫ φ → x₀'.left = x'.left ≫ φ → (x₀ * x₀').left = (x * x').left ≫ φ := by
    intro T x x' x₀ x₀' hx hx'
    haveI := mi₂
    haveI := mp₁
    have wx : ∀ z : T ⟶ c₂.A, ((z ≫ inc₂).left ≫ ψ) ≫ w₁.A.hom = (Over.mk (T.hom ≫ y)).hom := fun z => by
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w (z ≫ inc₂)]; rfl
    let X₀ : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x ≫ inc₂).left ≫ ψ) (wx x)
    let X₀' : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x' ≫ inc₂).left ≫ ψ) (wx x')
    have m := hψ.2 T (x ≫ inc₂) (x' ≫ inc₂) X₀ X₀' rfl rfl
    rw [← mul_comp] at m
    have e₀ : X₀ ≫ pr₁ = x₀ := by
      ext1
      rw [Over.comp_left, hx, hφ]
      show ((x ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    have e₀' : X₀' ≫ pr₁ = x₀' := by
      ext1
      rw [Over.comp_left, hx', hφ]
      show ((x' ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    rw [← e₀, ← e₀', ← mul_comp, Over.comp_left, m, hφ, Over.comp_left, Category.assoc, Category.assoc]
  have sq := ActUnr.sqMap_fst hw
  have sq' := ActUnr.sqMap_snd hw
  refine ⟨φ, ActUnr.sqMap hw, ⟨hpb, hmul⟩, ⟨sq, sq'⟩, ?_, fun a => ?_⟩
  · have f₁ : (inc₁ ⊗ₘ inc₁).left ≫ (fst w₁.A w₁.A).left = (fst c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₁ : (inc₁ ⊗ₘ inc₁).left ≫ (snd w₁.A w₁.A).left = (snd c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have f₂ : (inc₂ ⊗ₘ inc₂).left ≫ (fst w₂.A w₂.A).left = (fst c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₂ : (inc₂ ⊗ₘ inc₂).left ≫ (snd w₂.A w₂.A).left = (snd c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have E : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = ActUnr.sqMap hw ≫ (inc₁ ⊗ₘ inc₁).left := by
      apply ActUnr.left_hom_ext
      · rw [Category.assoc, sψ.1, ← Category.assoc, f₂]
        simp only [Category.assoc]
        rw [f₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq, Category.assoc, K1]
      · rw [Category.assoc, sψ.2, ← Category.assoc, g₂]
        simp only [Category.assoc]
        rw [g₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq', Category.assoc, K1]
    have l₂ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB w₂.isLB c₂.isLB lψ L₂
    have hN := pull_isLB c₁.isLB (ActUnr.sqMap hw)
    have l₁ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB c₁.isLB hN L₁ ((GlobalTheory.CechPic.cls_eq_iff hN hN).1 rfl)
    rw [E] at l₂
    exact LBIso.trans c₂.isLB (pull_isLB w₁.isLB _) hN l₂ (LBIso.symm l₁)
  · calc (c₂.lev a).left ≫ φ = (c₂.lev a ≫ inc₂).left ≫ ψ ≫ pr₁.left := by
          rw [hφ, Over.comp_left, Category.assoc]
      _ = (w₂.lev (jl a)).left ≫ ψ ≫ pr₁.left := by rw [V₂ a]
      _ = y ≫ (w₁.lev (jl a)).left ≫ pr₁.left := by rw [← Category.assoc, vψ, Category.assoc]
      _ = y ≫ (c₁.lev a).left := by rw [← V₁ a, Over.comp_left, Category.assoc, ip₁', Category.comp_id]

end GlobalTheory.UPel.HT

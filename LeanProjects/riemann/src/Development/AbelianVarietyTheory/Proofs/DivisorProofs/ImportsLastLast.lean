import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem even_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ (iT : T ⟶ T) (iT₁ : T₁ ⟶ T₁) (iT₂ : T₂ ⟶ T₂) {iG : G ⟶ G} {iG₁ : G₁ ⟶ G₁} {iG₂ : G₂ ⟶ G₂} {iB : B ⟶ B} {iB₁ : B₁ ⟶ B₁} {iB₂ : B₂ ⟶ B₂} (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (s₁ : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![iG₁, 𝟙 G₁] ![1, -1])) (s₂ : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![iG₂, 𝟙 G₂] ![1, -1])) (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (σ₁ : LB.Gen (LB.LinComb M₁ (K := Fin 2) ![iB₁, 𝟙 B₁] ![1, -1])) (σ₂ : LB.Gen (LB.LinComb M₂ (K := Fin 2) ![iB₂, 𝟙 B₂] ![1, -1])), iT ≫ h₁ = h₁ ≫ iT₁ → iT ≫ h₂ = h₂ ≫ iT₂ → iT ≫ f = f ≫ iG → iT ≫ p = p ≫ iB → iT₁ ≫ f₁ = f₁ ≫ iG₁ → iT₁ ≫ p₁ = p₁ ≫ iB₁ → iT₂ ≫ f₂ = f₂ ≫ iG₂ → iT₂ ≫ p₂ = p₂ ≫ iB₂ → IsBoxGen wL g₁ g₂ s s₁ s₂ → IsBoxGen wM b₁ b₂ σ σ₁ σ₂ → GlobalTheory.PowUnif.EvenAlong we₁ iT₁ s₁ σ₁ → GlobalTheory.PowUnif.EvenAlong we₂ iT₂ s₂ σ₂ → GlobalTheory.PowUnif.EvenAlong we iT s σ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ e₁ e₂ e₃ e₄ we Q iT iT₁ iT₂ iG iG₁ iG₂ iB iB₁ iB₂ s s₁ s₂ σ σ₁ σ₂
    ih₁ ih₂ iF iP iF₁ iP₁ iF₂ iP₂ Hs Hσ ev₁ ev₂
  intro jS jT cS cT V k₁ k₂ k₃ k₄
  refine unit_ext fun z hz => ?_
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT V k₁ k₂ k₃ k₄ (𝟙 T) z hz
  refine n₁.trans (Eq.trans ?_ n₂.symm)
  clear n₁ n₂
  obtain ⟨J, hJ, hJj⟩ := exists_good M hM z (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT cT
    (fun k => Set.mem_iInter.1 (k₁ hz) k)
  obtain ⟨N, hN, hNj⟩ := exists_good L hL z (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS cS
    (fun k => Set.mem_iInter.1 (k₄ hz) k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at hM₁ z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at hM₂ z
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at hL₁ z
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at hL₂ z

  have hb₁ : (p ≫ iB) ≫ b₁ = (h₁ ≫ p₁) ≫ iB₁ := by
    rw [← iP, Category.assoc, e₁, ← Category.assoc, ih₁, Category.assoc, iP₁, Category.assoc]
  have hb₂ : (p ≫ iB) ≫ b₂ = (h₂ ≫ p₂) ≫ iB₂ := by
    rw [← iP, Category.assoc, e₂, ← Category.assoc, ih₂, Category.assoc, iP₂, Category.assoc]
  have hg₁ : (f ≫ iG) ≫ g₁ = (h₁ ≫ f₁) ≫ iG₁ := by
    rw [← iF, Category.assoc, e₃, ← Category.assoc, ih₁, Category.assoc, iF₁, Category.assoc]
  have hg₂ : (f ≫ iG) ≫ g₂ = (h₂ ≫ f₂) ≫ iG₂ := by
    rw [← iF, Category.assoc, e₄, ← Category.assoc, ih₂, Category.assoc, iF₂, Category.assoc]
  have QQ : ∀ k, om wM z J₁ J₂ J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) *
        gw we ((![iT, 𝟙 T] : Fin 2 → _) k) z (J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
          (fun _ => N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) =
      gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
          (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) *
        gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
          (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) *
        om wL z N₁ N₂ N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have q := Q T iT z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      rw [iP, iF, ih₁, ih₂, hb₁, hb₂, hg₁, hg₂] at q
      simpa only [Matrix.cons_val_zero] using q
    · have q := Q T (𝟙 T) z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at q
      rw [e₁, e₂, e₃, e₄] at q
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Category.comp_id] using q
  have HM := Hσ T p z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂] at HM
  have HL := Hs T f z N₁ N₂ N hN₁ hN₂ hN
  rw [e₃, e₄] at HL
  have H₁ : val σ₁ (h₁ ≫ p₁) z J₁ = (∏ k, gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z
      (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
      (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₁ (h₁ ≫ f₁) z N₁ :=
    ev₁.stalk iF₁ iP₁ h₁ z _ _
      (fun a b e => congrArg N₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k))
      (fun k => hJ₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
  have H₂ : val σ₂ (h₂ ≫ p₂) z J₂ = (∏ k, gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z
      (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
      (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₂ (h₂ ≫ f₂) z N₂ :=
    ev₂.stalk iF₂ iP₂ h₂ z _ _
      (fun a b e => congrArg N₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k))
      (fun k => hJ₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
  have R := rel_alg (![1, -1] : Fin 2 → ℤ) _ _ _ _ _ QQ HM HL H₁ H₂
  rw [val_of σ p z J jT hJj, val_of s f z N jS hNj, Fin.prod_univ_two] at R
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg] at R
  have a₀ : J (p ≫ iB) = jT 0 := hJj 0
  have a₁ : J (p ≫ 𝟙 B) = jT 1 := hJj 1
  have c₀ : N (f ≫ iG) = jS 0 := hNj 0
  have c₁ : N (f ≫ 𝟙 G) = jS 1 := hNj 1
  rw [a₀, a₁, c₀, c₁] at R
  simp only [Category.id_comp]
  rw [R, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.ProdUnif

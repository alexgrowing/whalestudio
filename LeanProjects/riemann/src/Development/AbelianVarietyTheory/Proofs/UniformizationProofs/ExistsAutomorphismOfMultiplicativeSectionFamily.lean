import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingAutOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndRelAmpleLPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivPow

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SectionAut

abbrev PP {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => a)

theorem mem_one {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => p) j ↔ p y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem exists_equiv {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (PP L p N) n ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)),
      ∀ a (j : Fin 1 → L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart L (fun _ : Fin 1 => p) j →
        gs r z (LB.wchart L (fun _ : Fin 1 => p) j) ((E a).f j) =
          gs r z (LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := PowSections.exists_equiv L p N n
  refine ⟨E, fun a j Z r z hz => ?_⟩
  have le : LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hy
  have e : (E a).f j = (Y.presheaf.map (homOfLE le).op).hom (a.f (fun _ => j)) :=
    fn_ext fun y hy => (hE a j y (mem_one.1 hy)).trans (gs_res (𝟙 Y) y le hy _).symm
  exact (congrArg (gs r z _) e).trans (gs_res r z le hz _)

theorem exists_gen_of_iso {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) (F ψ : Y ⟶ Y) (hψ : ψ ≫ F = 𝟙 Y)
    (m : Y ⟶ X) (hm : ψ ≫ p = m) (w : LB.Iso (PP L p N) ((PP L p N).pull F)) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
      ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, m] j →
        gm (𝟙 Y) y (LB.wchart L ![p, m] j) (α.s j) = Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := by
  subst hm
  have hF : ∀ y, F (ψ y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      F (ψ y) ∈ (PP L p N).U (fun _ => j 0) := fun j y hy => by
    rw [hF]; exact mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      ψ y ∈ (PP L p N).U (fun _ => j 1) := fun j y hy => mem_one.2 (Set.mem_iInter.1 hy 1)
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L ![p, ψ ≫ p] j ≤
      ψ ⁻¹ᵁ (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) := fun j y hy =>
    ⟨mem_pull.2 (h0 j y hy), h1 j y hy⟩
  let α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, ψ ≫ p] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]) :=
    ⟨fun j => res (le j) (pullU ψ _ (w.s (fun _ _ => j 0, fun _ => j 1))) ^ (n : ℤ)⟩
  have hα : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      gm (𝟙 Y) y (LB.wchart L ![p, ψ ≫ p] j) (α.s j) =
        Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := fun j y hy =>
    (map_zpow _ _ _).trans (congrArg (· ^ (n : ℤ))
      ((gm_res (𝟙 Y) y (le j) hy _).trans (gm_pull (𝟙 Y) ψ y (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) (le j hy) _)))
  refine ⟨α, isGen_of_gm α fun y j j' hj hj' => ?_, hα⟩
  have e := (isGen_iff w).1 hw Y ψ y _ _ _ _ (h0 j y hj) (h0 j' y hj') (h1 j y hj) (h1 j' y hj')
  have e0 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (ψ ≫ F) y (fun _ => j 0) (fun _ => j' 0)
    (h0 j y hj) (h0 j' y hj')
  have e1 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) ψ y (fun _ => j 1) (fun _ => j' 1)
    (h1 j y hj) (h1 j' y hj')
  rw [Fin.prod_univ_one] at e0 e1
  have e' := e.trans (congrArg₂ (fun a b => a * b⁻¹ * _) e0 e1)
  rw [hα j y hj, hα j' y hj', e', trF, Fin.prod_univ_two, hψ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, mul_zpow, inv_zpow, ← zpow_mul,
    Nat.cast_mul, zpow_neg]

theorem chart_le {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def rho {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Γ(Y, LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) →+* Γ(Y, LB.wchart L (fun _ : Fin 1 => p) j) :=
  (Y.presheaf.map (homOfLE (chart_le L p N j)).op).hom

theorem rho_injective {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Function.Injective (rho L p N j) := fun a b h => fn_ext fun y hy => by
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => p) j := Set.mem_iInter.1 hy 0
  exact (gs_res (𝟙 Y) y (chart_le L p N j) hy' a).symm.trans ((congrArg (gs (𝟙 Y) y _) h).trans
    (gs_res (𝟙 Y) y (chart_le L p N j) hy' b))

theorem rho_resTop {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) (c : Γ(Y, ⊤)) :
    rho L p N j (resTop _ c) = resTop _ c := fn_ext fun y hy =>
  (gs_res (𝟙 Y) y (chart_le L p N j) hy _).trans ((gs_res (𝟙 Y) y le_top (chart_le L p N j hy) c).trans
    (gs_res (𝟙 Y) y le_top hy c).symm)

theorem exists_iso {K : Type} [CommRing K] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (Y : Over (Spec (CommRingCat.of K))) [IsProper Y.hom] (p : Y.left ⟶ X) (N : ℕ) (hA : RelAmple Y (PP L p N))
    (Φ : ∀ n : ℕ, 1 ≤ n → LB.Sec (PP L p ((N * n : ℕ) : ℤ)) ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)))
    (hlin : ∀ n hn (c : K) (s s' s'' : LB.Sec (PP L p ((N * n : ℕ) : ℤ))),
      (∀ j, s''.f j = resTop _ (scal Y.hom c) * s.f j + s'.f j) →
      ∀ j, (Φ n hn s'').f j = resTop _ (scal Y.hom c) * (Φ n hn s).f j + (Φ n hn s').f j)
    (hmul : ∀ n m hn hm hnm (s : LB.Sec (PP L p ((N * n : ℕ) : ℤ))) (s' : LB.Sec (PP L p ((N * m : ℕ) : ℤ)))
      (s'' : LB.Sec (PP L p ((N * (n + m) : ℕ) : ℤ))),
      (∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s''.f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s.f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s'.f j)) →
      ∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ (n + m) hnm s'').f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn s).f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ m hm s').f j)) :
    ∃ ψ : Y ≅ Y, ∀ (m : Y.left ⟶ X), ψ.hom.left ≫ p = m → ∀ n hn,
      ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
        ∀ s (j : Fin 2 → L.ι) (y : Y.left), y ∈ LB.wchart L ![p, m] j →
          gs (𝟙 _) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) ((Φ n hn s).f (fun _ => j 0)) =
            (gm (𝟙 _) y (LB.wchart L ![p, m] j) (α.s j)).val *
              gs ψ.hom.left y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  choose E hE using fun n => exists_equiv L p N n
  have hE' : ∀ n a j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((E n a).f j) =
      rho L p N j (a.f (fun _ => j)) := fun n a j =>
    fn_ext fun y hy => (hE n a j _ (𝟙 _) y hy).trans (gs_res (𝟙 _) y (chart_le L p N j) hy _).symm
  let θ : ∀ n : ℕ, 1 ≤ n → (H0 (PP L p N) n ≃ H0 (PP L p N) n) := fun n hn => (E n).trans ((Φ n hn).trans (E n).symm)
  have hθE : ∀ n hn a, E n (θ n hn a) = Φ n hn (E n a) := fun n hn a => (E n).apply_symm_apply _
  have hθ : ∀ n hn a j, rho L p N j ((θ n hn a).f (fun _ => j)) =
      @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn (E n a)).f j) := fun n hn a j => by
    rw [← hE', hθE]
  have one : ∀ j : Fin 1 → (PP L p N).ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
  obtain ⟨Φ₀, w, hw, H⟩ := exists_iso_of_sectionRing_aut_of_relAmple K Y (PP L p N) (LB.isLB_linComb hL _ _) hA θ
    (fun n hn c a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hlin n hn c (E n b) (E n a) (E n d) (fun j => (hE' n d j).trans ((congrArg (rho L p N j) (h _)).trans
        ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·) ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (rho_resTop L p N j _) (hE' n b j).symm)) (hE' n a j).symm))))) i
      exact (hθ n hn d i).trans (e.trans ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·)
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rho_resTop L p N i _) (hθ n hn b i))) (hθ n hn a i)))).symm))
    (fun n m hn hm a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hmul n m hn hm (hn.trans (Nat.le_add_right n m)) (E n a) (E m b) (E (n + m) d)
        (fun j => (hE' _ d j).trans ((congrArg (rho L p N j) (h _)).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hE' n a j).symm (hE' m b j).symm)))) i
      exact (hθ _ _ d i).trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hθ n hn a i) (hθ m hm b i))).symm))
  have hψ : Φ₀.inv.left ≫ Φ₀.hom.left = 𝟙 _ := by rw [← Over.comp_left, Φ₀.inv_hom_id, Over.id_left]
  refine ⟨Φ₀.symm, fun m hm n hn => ?_⟩
  obtain ⟨α, hα, hv⟩ := exists_gen_of_iso L p N n Φ₀.hom.left Φ₀.inv.left hψ m hm w hw
  refine ⟨α, hα, fun s j y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (E n).surjective s
  have hF : Φ₀.hom.left (Φ₀.inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0) := mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : Φ₀.inv.left y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1) := by
    subst hm; exact mem_one.2 (Set.mem_iInter.1 hy 1)
  have e := H n hn a _ Φ₀.inv.left y (fun _ _ => j 0) (fun _ _ => j 1)
    (fun _ => (congrArg (· ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) hF).mpr h0) (fun _ => h1)
  rw [hψ, Fin.prod_univ_one, Category.comp_id] at e
  rw [← hθE, hE n _ _ _ (𝟙 _) y h0, hv j y hy]
  exact e.trans (congrArg _ (hE n a _ _ Φ₀.inv.left y h1).symm)

end SectionAut

theorem exists_iso_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  intro F _ S P t N hN Φ hlin hmul
  obtain ⟨hp, hA⟩ := isProper_and_relAmple_lPow F S P t N hN
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hmul' : ∀ k l m (_ : m = k + l + 1) (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)))
      (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t)))
      (s'' : LB.Sec (LPow P.A P.L ((N * (m + 1) : ℕ) : ℤ) (Over.mk t))),
      (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) →
      ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ m s'').f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j) := by
    rintro k l _ rfl
    exact hmul k l
  obtain ⟨ψ₀, H⟩ := SectionAut.exists_iso P.L P.isLB
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) (snd (Over.mk t) P.A).left N hA
    (fun n hn => match n, hn with | k + 1, _ => Φ k)
    (fun n hn c => match n, hn with
      | k + 1, _ => fun s s' s'' => hlin k s s' s'' ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c))
    (fun n m hn hm _ => match n, m, hn, hm with
      | k + 1, l + 1, _, _ => hmul' k l (k + 1 + l) (by omega))
  have w₀ : ψ₀.hom.left ≫ (fst (Over.mk t) P.A).left = (fst (Over.mk t) P.A).left := Over.w ψ₀.hom
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A := Over.isoMk ((Over.forget _).mapIso ψ₀) (by
    have e : (fst (Over.mk t) P.A).left ≫ t = (Over.mk t ⊗ P.A).hom := Over.w (fst (Over.mk t) P.A)
    show ψ₀.hom.left ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t ⊗ P.A).hom
    rw [← e, ← Category.assoc, w₀])
  refine ⟨ψ, Over.OverMorphism.ext w₀, fun k => ?_⟩
  obtain ⟨α, hα, hv⟩ := H (ψ.hom ≫ snd _ _).left rfl (k + 1) (Nat.succ_pos k)
  refine ⟨α, hα, fun s j => fn_ext fun y hy => ?_⟩
  have l₀ := chart_le_zero P.A P.L (ψ.hom ≫ snd _ _) j
  have l₁ := chart_le_pull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl j
  exact (gs_res (𝟙 _) y l₀ hy _).trans ((hv s j y hy).trans ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) ((gs_res (𝟙 _) y l₁ hy _).trans
      (gs_pull (𝟙 _) ψ.hom.left y
        (LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) (fun _ => j 1)) (l₁ hy) _)))).symm)

end GlobalTheory

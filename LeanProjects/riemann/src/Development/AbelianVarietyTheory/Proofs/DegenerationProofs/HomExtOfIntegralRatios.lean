import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PolAVNonzeroLocusCoverAffine
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatioExt

open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem corresp_refl {X Z : Scheme.{0}} {L : LB X} {φ ψ : Z ⟶ X}
    (hc : ∀ N : ℕ, 4 ≤ N → ∀ x : X, ∃ s : H0 L N, x ∈ nonzeroLocus s)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (a b : H0 L n) (z : Z) (j j' : Fin 1 → L.ι), φ z ∈ ch L j → ψ z ∈ ch L j' →
      sv φ z a j * sv ψ z b j' = sv φ z b j * sv ψ z a j') :
    Corresp (L := L) (L' := L) (fun _ _ => Equiv.refl _) φ ψ := by
  intro n hn a b z
  refine ⟨?_, fun j j' _ hj hj' => h n hn a b z j j' hj hj'⟩
  have hk : 1 ≤ n * (3 + 1) := by omega
  obtain ⟨d, hd, -⟩ := presMul_refl.exists_pow hn b 3 _ hk rfl
  obtain ⟨c, hcφ⟩ := hc (n * (3 + 1)) (by omega) (φ z)
  obtain ⟨c', hcψ⟩ := hc (n * (3 + 1)) (by omega) (ψ z)
  obtain ⟨j, hj⟩ := exists_ch hcφ
  obtain ⟨j', hj'⟩ := exists_ch hcψ
  show φ z ∈ nonzeroLocus b ↔ ψ z ∈ nonzeroLocus b
  rw [mem_iff b φ z hj, mem_iff b ψ z hj']
  constructor
  · intro hb
    have e := h _ hk d c' z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := (hb.pow (3 + 1)).mul ((mem_iff c' ψ z hj').1 hcψ)
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_right u)
  · intro hb
    have e := h _ hk c d z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := ((mem_iff c φ z hj).1 hcφ).mul (hb.pow (3 + 1))
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_left u)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : Unif I D A G)
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))} (hw : w.IsGen)
    {n : ℕ} (hn : 1 ≤ n) (a : H0 A.L n) : ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ A.L.U j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i j ^ (n : ℤ)).val * powVal a (f ≫ U.gen.hom.left) z j) := by
  obtain ⟨s, hs⟩ := exists_move A.isLB U.LG.isLB hw (𝟙 _) (n : ℤ) (g₁ := 𝟙 A.A.left) U.gen.hom.left
    ((Category.comp_id _).trans (Category.id_comp _).symm) (g₂ := pullback.fst G.hom (jK R))
    (Category.id_comp _).symm a
  obtain ⟨F, ⟨r, hr, σ, -, h₁, -⟩, -⟩ := (U.expand n hn).1 s
  refine ⟨r, σ, hr, fun Z f z i j hi hj => ?_⟩
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Unit => f ≫ pullback.fst G.hom (jK R))
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have e₁ := ExpInt.secScal_sval h₁ f z hJ
  rw [sval_eq_powVal, sval_eq_powVal, Category.comp_id, e (), ExpInt.gs_scal, hs Z f z i j hi hj,
    Category.comp_id, ← Category.assoc] at e₁
  exact e₁

end GlobalTheory.RatioExt

namespace GlobalTheory

open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RatioExt in

theorem hom_ext_of_integral_ratios : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (P : ∀ k : ℕ, H0 U.LG.L k → Prop), (∀ k : ℕ, 1 ≤ k → ∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ : H0 U.LG.L k), c ≠ 0 ∧ (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ P k σ) → ∀ (Z : Scheme.{0}) (f₁ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left), f₁ ≫ pullback.snd G.hom (jK R) = f₂ ≫ pullback.snd G.hom (jK R) → (∀ z : Z, ∃ i₁ i₂ : U.LG.L.ι, (f₁ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₁ ∧ (f₂ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ σ τ : H0 U.LG.L k, P k σ → P k τ → gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (σ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (τ.f (fun _ => i₂)) = gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (τ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (σ.f (fun _ => i₂))) → f₁ = f₂ := by
  intro hL R _ _ I D A G _ _ U P hP Z f₁ f₂ hK h
  obtain ⟨w, hw⟩ := U.ext
  have key : ∀ n : ℕ, 1 ≤ n → ∀ a : H0 A.L n, ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧ P n σ ∧
      ∀ (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : Fin 1 → A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ ch A.L j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i (j 0) ^ (n : ℤ)).val * sv (f ≫ U.gen.hom.left) z a j) := fun n hn a => by
    obtain ⟨r, σ₀, hr, H⟩ := exists_integral U hw hn a
    obtain ⟨c, σ, hc, hσ, hPσ⟩ := hP n hn σ₀
    refine ⟨c * r, σ, mul_ne_zero hc hr, hPσ, fun f z i j hi hj => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun t => congrArg j (Subsingleton.elim _ _)⟩
    have e₁ := H Z f z i j hi (mem_wchart.1 hj 0)
    have e₂ : powVal σ (f ≫ pullback.fst G.hom (jK R)) z i = cst ((f ≫ pullback.fst G.hom (jK R)) ≫ G.hom) z c *
        powVal σ₀ (f ≫ pullback.fst G.hom (jK R)) z i :=
      secIsMul_gs (p := G.hom) (a := c) hσ _ z _ (mem_wchart.2 fun _ => hi)
    rw [Category.assoc, pullback.condition, ← Category.assoc] at e₂
    rw [e₂, e₁, H1.cst_mul, _root_.mul_assoc]
    rfl
  have := A.isAb.proper
  have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
  have : QuasiSeparatedSpace A.A.left := quasiSeparatedSpace_of_quasiSeparated A.A.hom
  have hc := fun N hN => (polAV_nonzeroLocus_cover_affine hL.ample A (N := N) hN).1
  have h₁ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₁ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) := by
    refine corresp_refl hc fun n hn a b z j j' hj hj' => ?_
    obtain ⟨i₁, i₂, m₁, m₂, H⟩ := h z
    obtain ⟨r, σ, hr, hσ, Hσ⟩ := key n hn a
    obtain ⟨s, τ, hs, hτ, Hτ⟩ := key n hn b
    have e : powVal σ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal τ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ =
        powVal τ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal σ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ :=
      H n hn σ τ hσ hτ
    rw [Hσ f₁ z i₁ j m₁ hj, Hσ f₂ z i₂ j' m₂ hj', Hτ f₁ z i₁ j m₁ hj, Hτ f₂ z i₂ j' m₂ hj', hK] at e
    refine ((((ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hr).mul
      (ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hs)).mul
      (isoVal w f₁ z i₁ (j 0) ^ (n : ℤ)).isUnit).mul (isoVal w f₂ z i₂ (j' 0) ^ (n : ℤ)).isUnit).mul_left_cancel ?_
    linear_combination e
  have h₂ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₂ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) :=
    corresp_refl hc fun n hn a b z j j' hj hj' => by
      refine (congrArg₂ (· * ·) (sec_trans a _ z hj hj') rfl).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (sec_trans b _ z hj hj') rfl).symm)
      exact (mul_right_comm _ _ _)
  have e := h₁.unique A.isLB h₂ (n := 4) (by norm_num) id
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc 4 le_rfl x))
    (polAV_nonzeroLocus_cover_affine hL.ample A le_rfl).2
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact (cancel_mono _).1 e

end GlobalTheory

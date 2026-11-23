import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorClassEqOfLocalStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.GenDivRatio

theorem det_fin_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 1) R M) (v : Fin 1 → M) : b.det v = b.repr (v 0) 0 := by
  rw [Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply]; rfl

theorem eq_repr_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 1) R M) (s : M) : s = b.repr s 0 • b 0 := by
  conv_lhs => rw [← b.sum_repr s]
  rw [Fin.sum_univ_one]

end GlobalTheory.GenDivRatio

theorem GlobalTheory.GenDivRatio.cls_div_eq_of_isRatio : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (A : B.X.Opens) (G G' : B.X.Modules) (hG : IsVB G 1) (hG' : IsVB G' 1) (ψ : G' ⟶ G) (φ : B.GenIso G G'), φ.inv = B.genRes.map ψ → genericPoint B.X ∈ A → ∀ (σ : Fin 1 → Γ(G', A)) (hσ' : IsFrame σ) (hσ : IsFrame fun i => ψ.app A (σ i)) (L L' : LB B.X) (ρ : ∀ k, Γ(B.X, A ⊓ L.U k)) (ρ' : ∀ k, Γ(B.X, A ⊓ L'.U k)), IsGenOn A L ρ → IsGenOn A L' ρ' → Tri hσ (fun _ => L) (fun _ => ρ) → Tri hσ' (fun _ => L') (fun _ => ρ') → ∀ D : VertDiv B, IsRatio A D L L' ρ ρ' → (φ.div hG hG').cls = D.cls := by
  intro O _ _ _ B A G G' hG hG' ψ φ hψ hA σ hσ' hσ L L' ρ ρ' hgen hgen' htri htri' D hrat
  refine GlobalTheory.T.cartier_divisor_class_eq_of_local O B (φ.div hG hG') D fun x => ?_
  obtain ⟨V, e, k, hk, hxV, he, -, hce⟩ := htri x
  obtain ⟨V', e', k', hk', hxV', he', -, hce'⟩ := htri' x
  obtain ⟨j, k₁, k₁', hxj, hxk₁, hxk₁', hR⟩ := hrat x
  let c : Chart G 1 := ⟨V, e, he⟩
  let c' : Chart G' 1 := ⟨V', e', he'⟩
  let V₀ : B.X.Opens := V ⊓ V' ⊓ D.M.U j ⊓ L.U k₁ ⊓ L'.U k₁'
  have h₀V : V₀ ≤ V := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have h₀V' : V₀ ≤ V' := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have h₀j : V₀ ≤ D.M.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have h₀k₁ : V₀ ≤ L.U k₁ := inf_le_left.trans inf_le_right
  have h₀k₁' : V₀ ≤ L'.U k₁' := inf_le_right
  have h₀k : V₀ ≤ L.U (k 0) ⊓ L.U k₁ := le_inf (h₀V.trans (hk 0)) h₀k₁
  have h₀k' : V₀ ≤ L'.U (k' 0) ⊓ L'.U k₁' := le_inf (h₀V'.trans (hk' 0)) h₀k₁'
  have hx₀ : x ∈ V₀ := ⟨⟨⟨⟨hxV, hxV'⟩, hxj⟩, hxk₁⟩, hxk₁'⟩
  have hi : V₀ ≤ (φ.div hG hG').M.U (c, c') := le_inf h₀V h₀V'
  refine ⟨V₀, (c, c'), j, hi, h₀j,
    res h₀k' (L'.g (k' 0) k₁') * (res h₀k (L.g (k 0) k₁))⁻¹, hx₀, ?_⟩
  set u := res h₀k' (L'.g (k' 0) k₁') * (res h₀k (L.g (k 0) k₁))⁻¹ with hu_def
  let W : B.X.Opens := B.gen ⊓ V₀ ⊓ A
  have hW : W ≤ B.gen ⊓ V₀ := inf_le_left
  have hWA : W ≤ A := inf_le_right
  have hW₀ : W ≤ V₀ := hW.trans inf_le_right
  have hWV : W ≤ V := hW₀.trans h₀V
  have hWV' : W ≤ V' := hW₀.trans h₀V'
  have hWVV' : W ≤ V ⊓ V' := le_inf hWV hWV'
  have hη : genericPoint B.X ∈ W :=
    ⟨⟨B.genericPoint_mem_gen, VB.genericPoint_mem hx₀⟩, hA⟩
  refine Cartier.ext_germK fun _ => ?_
  rw [← Cartier.germ_resG hW _ hη, ← Cartier.germ_resG hW _ hη]
  refine congrArg _ ?_
  have hWk : W ≤ A ⊓ L.U (k 0) := le_inf hWA (hWV.trans (hk 0))
  have hWk' : W ≤ A ⊓ L'.U (k' 0) := le_inf hWA (hWV'.trans (hk' 0))
  have hWk₁ : W ≤ A ⊓ L.U k₁ := le_inf hWA (hW₀.trans h₀k₁)
  have hWk₁' : W ≤ A ⊓ L'.U k₁' := le_inf hWA (hW₀.trans h₀k₁')
  have hWkk : W ≤ L.U (k 0) ⊓ L.U k₁ := hW₀.trans h₀k
  have hWkk' : W ≤ L'.U (k' 0) ⊓ L'.U k₁' := hW₀.trans h₀k'
  have hWj : W ≤ B.gen ⊓ D.M.U j := le_inf (hW.trans inf_le_left) (hW₀.trans h₀j)
  have hWP : W ≤ B.gen ⊓ (V ⊓ V') := le_inf (hW.trans inf_le_left) hWVV'
  rw [map_mul, VertDiv.resG_eqn, LB.resG_resG]
  erw [(φ.div hG hG').resG_eqn (c, c')]
  show D.eqn j hWj = resG B.X hW₀ u.val * (φ.div hG hG').eqn (c, c') hWP

  set r := resG B.X hWk (ρ (k 0)) with hr
  set r' := resG B.X hWk' (ρ' (k' 0)) with hr'
  have hcr : (hσ.basis hWA).repr (resM G hWV (e 0)) 0 = r := by
    have h1 := hσ.repr_resM (inf_le_right : V ⊓ A ≤ A) (le_inf hWV hWA) (resM G inf_le_left (e 0)) 0
    have h2 := hce 0
    simp only [coordIn] at h2
    rw [Twist.resM_resM, h2, LB.resG_resG] at h1
    exact h1
  have hcr' : (hσ'.basis hWA).repr (resM G' hWV' (e' 0)) 0 = r' := by
    have h1 := hσ'.repr_resM (inf_le_right : V' ⊓ A ≤ A) (le_inf hWV' hWA) (resM G' inf_le_left (e' 0)) 0
    have h2 := hce' 0
    simp only [coordIn] at h2
    rw [Twist.resM_resM, h2, LB.resG_resG] at h1
    exact h1
  have hψe' : ψ.app W (resM G' hWV' (e' 0)) = r' • (hσ.basis hWA) 0 := by
    have h1 := GenDivRatio.eq_repr_smul (hσ'.basis hWA) (resM G' hWV' (e' 0))
    rw [hcr', IsFrame.basis_apply] at h1
    rw [h1, Scheme.Modules.Hom.app_smul, Twist.app_resM, IsFrame.basis_apply]
  have hunit : IsUnit r := by
    have : r = (hσ.detUnit he hWA hWV : Γ(B.X, W)) := by
      rw [IsFrame.val_detUnit, GenDivRatio.det_fin_one, hcr]
    exact this ▸ Units.isUnit _
  have hp := Model.GenIso.eqn_div_of_hom hG hG' hψ c c' hWP le_rfl
  rw [GenDivRatio.det_fin_one] at hp
  set a := ((c.isFrame.basis (le_rfl.trans inf_le_left)).repr
    (ψ.app (V ⊓ V') (resM G' (le_rfl.trans inf_le_right) (c'.e 0)))) 0 with ha
  have hq := GenDivRatio.eq_repr_smul (c.isFrame.basis (le_rfl.trans inf_le_left))
    (ψ.app (V ⊓ V') (resM G' (le_rfl.trans inf_le_right) (c'.e 0)))
  rw [← ha, IsFrame.basis_apply] at hq
  have hq2 := congrArg (resM G hWVV') hq
  rw [← Twist.app_resM, Twist.resM_resM, Twist.resM_smul, Twist.resM_resM] at hq2
  change ψ.app W (resM G' hWV' (e' 0)) = _ at hq2
  rw [hψe'] at hq2
  have hq3 := congrArg (fun s => (hσ.basis hWA).repr s 0) hq2
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
    Finsupp.single_eq_same, mul_one] at hq3
  change r' = _ * (hσ.basis hWA).repr (resM G hWV (e 0)) 0 at hq3
  rw [hcr] at hq3
  rw [hp]
  have hR' := hR W hWj hWk₁ hWk₁'
  have hg := hgen (k 0) k₁ W hWk hWk₁ hWkk
  have hg' := hgen' (k' 0) k₁' W hWk' hWk₁' hWkk'
  rw [← hr] at hg
  rw [← hr'] at hg'
  rw [hg, hg'] at hR'
  have hu : resG B.X hW₀ u.val * resG B.X hWkk (L.g (k 0) k₁).val =
      resG B.X hWkk' (L'.g (k' 0) k₁').val := by
    have h1 : u * res h₀k (L.g (k 0) k₁) = res h₀k' (L'.g (k' 0) k₁') := by
      rw [hu_def]; exact inv_mul_cancel_right _ _
    have h2 := congrArg (fun v : Γ(B.X, V₀)ˣ => resG B.X hW₀ v.val) h1
    simp only [Units.val_mul, map_mul, LB.val_res, LB.resG_resG] at h2
    exact h2
  have hγ : IsUnit (resG B.X hWkk (L.g (k 0) k₁).val) := (Units.isUnit _).map _
  have key : (D.eqn j hWj - resG B.X hW₀ u.val * resG B.X hWVV' a) *
      (resG B.X hWkk (L.g (k 0) k₁).val * r) = 0 := by
    linear_combination hR' - r' * hu + resG B.X hW₀ u.val * resG B.X hWkk (L.g (k 0) k₁).val * hq3
  exact sub_eq_zero.1 ((hγ.mul hunit).mul_left_eq_zero.1 key)

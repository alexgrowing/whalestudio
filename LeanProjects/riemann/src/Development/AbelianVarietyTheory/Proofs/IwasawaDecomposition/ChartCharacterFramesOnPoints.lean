import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

theorem chr_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q), g ∈ UAd hc n → ∀ (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → FrExact q g r.1.1 → FrExact q (g * z.1) (ya Λ Θ κ r).1.1 → ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  intro X n ST SG Q y _ hc σ Λ Θ r C D q g z hg κ h1 hE hE'
  obtain ⟨γ, h, θ⟩ := κ
  have hγ : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
  subst hγ

  have hzU : z.1 ∈ levU hc n ST SG (chG Λ C) := levUQ_le q _ z.2
  have hx : g * z.1 ∈ UAd hc n := mul_mem hg (levU_le_UAd hc n ST SG _ hzU)
  have hdeco : decoOf ST SG (g * z.1) = ((1, h.1) : UF X.E n × GLG X.E n SG) • decoOf ST SG g := by
    rw [hE'.1, hE.1]
    rfl
  have e2 : decoRaw ST SG (g * z.1) = (decoRaw ST SG g).act 1 h.1 := by
    rw [← rlc_decoOf_val hc n ST SG hx, ← rlc_decoOf_val hc n ST SG hg, hdeco]
    rfl
  obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hx hg h.1 e2
  have e3 : z.1 = ((g * z.1)⁻¹ * g)⁻¹ := by group
  have hJ' : z.1 ∈ J0 hc n ST := e3 ▸ inv_mem hJ
  have hr' : redG hc n ST SG ⟨z.1, hJ'⟩ = h.1⁻¹ := by
    rw [← hr, ← map_inv]
    exact congrArg _ (Subtype.ext e3)
  have hA : levTyp (chLam σ Λ C) (Subgroup.inclusion (levUQ_le q _) z) = (Units.map σ.toMonoidHom (Λ.chr h)) := by
    have h2 : Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) z)) = h⁻¹ :=
      Subtype.ext hr'
    show (Units.map σ.toMonoidHom (Λ.chr (Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) z)))))⁻¹ = _
    rw [h2, map_inv, map_inv, inv_inv]

  have hP : ∀ P : Q, q.at P z.1 = Formalism.UG.bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := fun P => by
    have a1 := hE.2 P
    have a2 := hE'.2 P
    have efr : (ya Λ Θ ((1 : UF X.E n), h, θ) r).1.1.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      show (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * r.1.1.fr P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
    have a3 : q.at P (g * z.1) = q.at P g * q.at P z.1 := by
      simp only [QLoc.at, map_mul]
    rw [a3, a1, efr] at a2
    simp only [qGL, map_mul] at a2
    exact mul_left_cancel a2
  have hB : ∀ P : Q, q.chr P (lqRes q (chG Λ C) P z) = ((Θ P).lam ⟨θ.1 P, θ.2 P trivial⟩)⁻¹ := fun P => by
    have hmem : Formalism.UG.bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) ∈ q.U P := hP P ▸ (lqRes q (chG Λ C) P z).2
    have hcut : (θ.1 P)⁻¹ ∈ (cutQ Θ D P).H := (q.U_rat P _).1 hmem
    have e4 : lqRes q (chG Λ C) P z = ⟨_, hmem⟩ := Subtype.ext (hP P)
    rw [e4, q.chr_rat P _ hcut hmem, ← map_inv]
    rfl
  have hT : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, θ.2 P trivial⟩ := by
    unfold LevQFam.chr piChar
    erw [MonoidHom.finsetProd_apply]
    rfl
  have hC : chiQ q (chG Λ C) σ z = (Units.map σ.toMonoidHom (Θ.chr θ))⁻¹ := by
    unfold chiQ
    rw [MonoidHom.finsetProd_apply, hT, map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hB P, map_inv]
  show ((levTyp (chLam σ Λ C) (Subgroup.inclusion (levUQ_le q _) z) * (chiQ q (chG Λ C) σ z)⁻¹ : ℂˣ) : ℂ) = _
  rw [hA, hC, inv_inv, ← map_mul]
  rfl

end GlobalTheory.Mem.Col2.ChEx

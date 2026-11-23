import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndexStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjProjOfGood

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShVac

theorem le_sup_of_coprime {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} {s m : ℕ}
    (h : s.Coprime m) (hB : ∀ y ∈ A, s • y ∈ B) (hC : ∀ y ∈ A, m • y ∈ C) :
    A ≤ (A ⊓ B) ⊔ (A ⊓ C) := by
  intro y hy
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : y = a • s • y + b • m • y := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact AddSubgroup.add_mem_sup
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hB y hy⟩) _)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hC y hy⟩) _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ}

omit [IsCMField E] in
theorem nsmul_tens {Λ Λ' : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, ∀ u ∈ L, k • vecMulVec v u ∈ tens Λ' L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L' := by
  have : tens Λ L ≤ (tens Λ' L').comap (nsmulAddMonoidHom k) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact h v hv u hu
  exact fun y hy => this hy

omit [IsCMField E] in
theorem nsmul_tens_left {Λ Λ' : Lt E n} {L : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, (k : E) • v ∈ Λ') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨_, h v hv, u, hu, by
    ext i j; simp [vecMulVec_apply, _root_.mul_assoc]⟩

omit [IsCMField E] in
theorem nsmul_tens_right {Λ : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ u ∈ L, (k : 𝓞 E) • u ∈ L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ L' :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨v, hv, _, h u hu, by
    rw [Nat.cast_smul_eq_nsmul]
    ext i j; simp [vecMulVec_apply, mul_left_comm]⟩

omit [IsCMField E] in
theorem relIndex_half {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L).toAddSubgroup.relIndex (L ⊓ L').toAddSubgroup ∧
    ∀ x ∈ L', x ∈ idq P Q L → x ∈ idq P Q L' := by
  obtain ⟨a, m, hm, e⟩ := Lev.cop_iff.1 hs
  have d (x : Fin r → E) : x = a • s • x + m • x := by
    rw [← mul_smul, ← add_smul, e, one_smul]
  constructor
  · refine Lev.relIndex_eq (fun x hx => hx.1) fun x (hx : x ∈ L) => ?_
    rw [d x]
    exact AddSubgroup.add_mem_sup ⟨L.smul_mem _ (L.smul_mem _ hx), L'.smul_mem _ (h x hx)⟩
      ⟨fun b _ => Submodule.smul_mem _ b (Submodule.smul_mem_smul hm hx), L.smul_mem _ hx⟩
  · intro x hx H b hb
    rw [d (b • x)]
    exact add_mem (Submodule.smul_mem _ _ (Lev.smul_map_mem LinearMap.id h (H b hb)))
      (Submodule.smul_mem_smul hm (L'.smul_mem _ hx))

omit [IsCMField E] in

theorem relIndex_shift {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') (h' : ∀ v ∈ L', s • v ∈ L) :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L').toAddSubgroup.relIndex L'.toAddSubgroup := by
  obtain ⟨h1, h2⟩ := relIndex_half (Q := Q) hs h
  obtain ⟨h3, h4⟩ := relIndex_half (Q := Q) hs h'
  rw [h1, h3, inf_comm L' L, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (idq P Q L').toAddSubgroup]
  congr 1
  ext x
  exact and_congr_left fun hx => ⟨h2 x hx.2, h4 x hx.1⟩

theorem eq_sqrt {k t : ℝ} (ht : 0 ≤ t) (h : k * t ^ 2 = 1) : t = √(k⁻¹) ∧ 0 < t := by
  refine ⟨?_, ht.lt_of_ne ?_⟩
  · rw [← eq_inv_of_mul_eq_one_right h, Real.sqrt_sq ht]
  · rintro rfl
    simp at h

theorem smul_eq_unitv {g : ℕ} {u : TF n g} (hu : IsSB u) (h1 : SW.ip u u = 1) {a : ℂ} (ha : 0 < ‖a‖) :
    a • u = ((‖a‖ : ℝ) : ℂ) • unitv (a • u) := by
  rw [unitv, TensVac.ip_smul_left _ hu (TensVac.sb_smul _ hu), TensVac.ip_smul_right _ hu hu, h1, _root_.mul_one,
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq ha.le, smul_smul (_ : ℂ) (_ : ℂ)⁻¹,
    mul_inv_cancel₀ (by exact_mod_cast ha.ne'), one_smul]

theorem shift_vac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n M, 0 < s Λ ∧ projA X bas D.w (tens Λ (D.sh L)) (projA X bas D.w (tens Λ L) v) = (t * (s Λ : ℂ)) • unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
  intro E _ _ _ r X g bas idx n hs hn D M _ hM v₀ hv₀
  have one {Λ} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
    obtain ⟨h1, h2, s, h3, -, h4⟩ := h
    exact ⟨h1, h2, s, h3, Nat.coprime_one_right s, h4⟩
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hsh {L} (hL : L ∈ D.lats) : SelfD X (D.sh L) := Lev.selfD_idq D.ne_bot D.proper D.cop hL.1
  have vac := TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have ten := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have pp := GlobalTheory.Dict.ProjProj.proj_proj E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have hΛ₀ : X.Λ ∈ D.lats := ⟨Lev.selfD_of_sympl hs, 1, Lev.cop_one, fun v hv => by simpa using hv,
    fun v hv => by simpa using hv⟩
  have key : ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v →
      ‖SW.ip v (v₀ L)‖ = √((((D.sh X.Λ).toAddSubgroup.relIndex X.Λ.toAddSubgroup ^ n : ℕ) : ℝ)⁻¹) ∧
        0 < ‖SW.ip v (v₀ L)‖ := by
    intro L hL v hv
    have h := (vac L hL.1 1 _ hstd).2.2.2 _ (hsh hL) _ hstd v _ hv (hv₀ L hL)
    rw [((ten L hL.1 1 _ hstd).2.2.2.2.1 _ (hsh hL)).1] at h
    obtain ⟨-, s, h1, h2, h3⟩ := hL
    rw [Level.sh, relIndex_shift h1.of_mul_right_left h2 h3] at h
    exact eq_sqrt (norm_nonneg _) h
  refine ⟨_, fun Λ => √(((Λ.toAddSubgroup.relIndex (stdL E n).toAddSubgroup ^ r : ℕ) : ℝ)⁻¹), ?_,
    fun L hL v hv => ⟨_, (key L hL v hv).1, fun Λ hΛ => ?_⟩⟩
  · obtain ⟨v, hv⟩ := (vac _ hΛ₀.1 1 _ hstd).1
    exact (key _ hΛ₀ v hv).1 ▸ (key _ hΛ₀ v hv).2
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := vac _ (hsh hL) 1 _ (one hΛ)
  have h := (vac _ (hsh hL) 1 _ hstd).2.2.2 _ (hsh hL) _ (one hΛ) _ u (hv₀ L hL) hu
  rw [(ten _ (hsh hL) 1 _ hstd).2.2.2.2.2 _ (one hΛ)] at h
  obtain ⟨h1, h2⟩ := eq_sqrt (norm_nonneg _) h
  simp only [← h1]
  refine ⟨h2, ?_⟩
  obtain ⟨s, -, hc, s1, s2⟩ := hΛ.2.2
  have hM' : (M : 𝓞 E) ∈ conjI D.𝔪 := Lev.mem_conjI.2 (by rwa [map_natCast])
  have e1 := pp L L _ hL.1 hL.1 (hsh hL) _ hstd _ (one hΛ) _ (one hΛ)
    (le_sup_of_coprime hc (nsmul_tens_left s1) (nsmul_tens_right fun x hx =>
      Lev.smul_le_idq _ _ _ (Submodule.smul_mem_smul hM hx))) v hv
  have e2 := pp L _ _ hL.1 (hsh hL) (hsh hL) _ hstd _ hstd _ (one hΛ)
    (le_sup_of_coprime hc.symm (nsmul_tens_right fun x hx => Submodule.smul_le_right (hx _ hM'))
      (nsmul_tens_left s2)) v hv
  have b₀ := (hv₀ L hL).1
  rw [e1, ← e2, (vac _ (hsh hL) 1 _ hstd).2.2.1 v hv.1 _ (hv₀ L hL), hp _ (TensVac.sb_smul _ b₀) u hu,
    hp _ b₀ u hu, TensVac.ip_smul_left _ b₀ hu.1, mul_smul, mul_smul, ← smul_eq_unitv hu.1 hu.2.1 h2]

end GlobalTheory.Dict.ShVac

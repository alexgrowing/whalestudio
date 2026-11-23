import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkRootMultiplicationScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkFrobeniusScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkPresentationInvariantStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ChainPeriod

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime] [CharZero O]
  {B : Vert.Model O}

theorem isIso_genRes_smulHom_of_root (E : B.X.Modules) {π : Γ(B.X, ⊤)} (h : IsRootOfP p π (p - 1)) :
    IsIso (B.genRes.map (smulHom E π)) := by
  rw [VB.pullback_map_smulHom]
  have hp : IsUnit ((Scheme.Hom.appTop B.gen.ι).hom (B.const (p : O))) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top B.gen.ι _).le (B.gen_le_basicOpen (natCast_ne_zero O p) x.2))
  obtain ⟨u, hu⟩ := h
  have hc : B.const (p : O) = (p : Γ(B.X, ⊤)) := map_natCast _ p
  rw [hc] at hp
  have hpow : IsUnit (((Scheme.Hom.appTop B.gen.ι).hom π) ^ (p - 1)) := by
    rw [← map_pow, hu, map_mul]
    exact (u.isUnit.map _).mul hp
  have hπ := (isUnit_pow_iff (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)).1 hpow
  exact (isUnit_iff_isIso _).1 (hπ.map (smulEnd _))

end GlobalTheory.ChainPeriod

open GlobalTheory.ChainPeriod in

theorem GlobalTheory.MixedLocalChains.Chain.ck_period : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (ι : Type) (φ : ι → ι) (o : ℕ) (Ch : Chain p B φ o), (∀ τ, φ^[o] τ = τ) → ∀ (k : ℕ) (La : ι → PicSym B.X →ₗ[ℚ] ℚ), (∀ τ, La τ = ckP p (GlobalTheory.Vert.Model.GenIso.smul (Ch.lw τ).E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) (Ch.lw τ).r k) → ∀ τ, (1 - ((p : ℚ) ^ (o * k))⁻¹) • ((Ch.oo τ).ck p k - (Ch.lw τ).ck p k + ((p : ℚ) - 1)⁻¹ • La τ) = ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ • La (φ^[n + 1] τ) := by
  intro O _ _ _ p _ _ _ B hB ι φ o Ch hper k La hLa τ
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hiso_pi : ∀ τ, IsIso (B.genRes.map (smulHom (Ch.lw τ).E' Ch.π)) :=
    fun τ => isIso_genRes_smulHom_of_root _ Ch.π_root
  have hiso_wl : ∀ τ, IsIso (B.genRes.map (Ch.wl τ)) := by
    intro τ
    haveI := (Ch.lw τ).iso
    haveI h2 := hiso_pi τ
    rw [← Ch.lw_wl τ, Functor.map_comp] at h2
    exact IsIso.of_isIso_comp_left (B.genRes.map (Ch.lw τ).ψ) (B.genRes.map (Ch.wl τ))
  let Ppi : ι → Pres B := fun τ => ⟨(Ch.lw τ).r, (Ch.lw τ).E', (Ch.lw τ).E', (Ch.lw τ).vb', (Ch.lw τ).vb',
    smulHom _ Ch.π, hiso_pi τ⟩
  let Pwl : ι → Pres B := fun τ => ⟨(Ch.lw τ).r, (Ch.lw τ).E', (Ch.lw τ).E, (Ch.lw τ).vb', (Ch.lw τ).vb,
    Ch.wl τ, hiso_wl τ⟩
  let Pp : ι → Pres B := fun τ => ⟨(Ch.lw τ).r, (Ch.lw τ).E', (Ch.lw τ).E', (Ch.lw τ).vb', (Ch.lw τ).vb',
    smulHom _ (B.const (p : O)), Vert.Model.isIso_genRes_map_smulHom _ (natCast_ne_zero O p)⟩
  have hPp : ∀ τ, (Pp τ).ck p k = La τ := fun τ => by rw [hLa]; rfl
  have hpi : ∀ τ, (Ppi τ).ck p k = (Pwl τ).ck p k + (Ch.lw τ).ck p k := by
    intro τ
    have := (GlobalTheory.T.ck_additive_composition O p B hB _ _ _ (haveI := hiso_wl τ; Vert.Model.GenIso.ofHom (Ch.wl τ))
      (haveI := (Ch.lw τ).iso; Vert.Model.GenIso.ofHom (Ch.lw τ).ψ) (Ch.lw τ).r k (Ch.lw τ).vb' (Ch.lw τ).vb
      (Ch.lw τ).vb').1
    refine Eq.trans ?_ this
    have heq : (@Vert.Model.GenIso.ofHom _ _ _ _ _ _ _ (smulHom _ Ch.π) (hiso_pi τ)) =
        ((haveI := hiso_wl τ; Vert.Model.GenIso.ofHom (Ch.wl τ)) ≪≫
          (haveI := (Ch.lw τ).iso; Vert.Model.GenIso.ofHom (Ch.lw τ).ψ)) := by
      refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
      simp only [Vert.Model.GenIso.ofHom, Iso.trans_inv, Iso.symm_inv, asIso_hom]
      rw [← Functor.map_comp, Ch.lw_wl]
    show ckP p (@Vert.Model.GenIso.ofHom _ _ _ _ _ _ _ (smulHom _ Ch.π) (hiso_pi τ)) _ k = _
    rw [heq]
  have hbd : ∀ τ, (((p - 1 : ℕ) : ℚ)) • (Ppi τ).ck p k = La τ := by
    intro τ
    rw [hLa τ]
    exact (GlobalTheory.T.ck_root_multiplication_scaling O p B hB (Ppi τ) Ch.π (p - 1) (Iso.refl _) Ch.π_root (Category.id_comp _).symm k).1
  have hc3 : ∀ τ, (Ch.q 0 τ).ck p k = (Pwl τ).ck p k + (Ch.oo τ).ck p k :=
    fun τ => GlobalTheory.T.ck_additive_extension O p B hB (Pwl τ) _ _ (Ch.c3 τ) k
  have hq0 : ∀ τ, (Ch.q 0 τ).ck p k = (Ch.oo τ).ck p k - (Ch.lw τ).ck p k + ((p : ℚ) - 1)⁻¹ • La τ := by
    intro τ
    have hp1 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      rw [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
    have hne : (p : ℚ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt.ne')
    rw [← hbd τ, hp1, smul_smul, inv_mul_cancel₀ hne, one_smul, hpi τ, hc3 τ]
    abel
  have hl : ∀ n < o, ∀ τ, (Ch.l n 0 τ).ck p k = ((p : ℚ) ^ ((n + 1) * k))⁻¹ • La (φ^[n + 1] τ) := by
    intro n hn τ
    have hi : ∀ i ≤ n + 1, (Ch.l n i τ).ck p k = ((p : ℚ) ^ k) ^ i • (Ch.l n 0 τ).ck p k := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        have hfr := Ch.l_frob n hn i (by omega) τ
        rw [GlobalTheory.T.ck_frobenius_scaling O p B hB _ _ Ch.g Ch.g_root hfr.1 hfr.2 k, ih (by omega), smul_smul, ← pow_succ']
    have hlast : (Ch.l n (n + 1) τ).ck p k = La (φ^[n + 1] τ) := by
      rw [← hPp]
      refine GlobalTheory.T.ck_presentation_invariant O p B hB _ _ ?_ k
      obtain ⟨e⟩ := Ch.l_last n hn τ
      have hc : B.const (p : O) = (p : Γ(B.X, ⊤)) := map_natCast _ p
      show Nonempty (_ ≅ cokernel (smulHom _ (B.const (p : O))))
      rw [hc]
      exact ⟨e⟩
    rw [hi (n + 1) le_rfl] at hlast
    rw [← hlast, smul_smul, ← pow_mul, mul_comm k, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_smul]
  have hq : ∀ m ≤ o, ∀ τ, (Ch.q m τ).ck p k = ((p : ℚ) ^ (m * k))⁻¹ • (Ch.q 0 (φ^[m] τ)).ck p k := by
    intro m
    induction m with
    | zero => intro _ τ; simp
    | succ m ih =>
      intro hm τ
      have hfr := Ch.q_frob m (by omega) τ
      have e := GlobalTheory.T.ck_frobenius_scaling O p B hB _ _ Ch.g Ch.g_root hfr.1 hfr.2 k
      rw [ih (by omega) (φ τ)] at e
      have hpk : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ hp0
      rw [Function.iterate_succ_apply]
      calc (Ch.q (m + 1) τ).ck p k = ((p : ℚ) ^ k)⁻¹ • ((p : ℚ) ^ k • (Ch.q (m + 1) τ).ck p k) := by
            rw [smul_smul, inv_mul_cancel₀ hpk, one_smul]
        _ = _ := by
            rw [← e, smul_smul, ← mul_inv, ← pow_add, show k + m * k = (m + 1) * k by ring]
  have hsum : ∀ m ≤ o, ∀ τ, (Ch.q 0 τ).ck p k =
      (Ch.q m τ).ck p k + ∑ n ∈ Finset.range m, (Ch.l n 0 τ).ck p k := by
    intro m
    induction m with
    | zero => intro _ τ; simp
    | succ m ih =>
      intro hm τ
      rw [ih (by omega) τ, GlobalTheory.T.ck_additive_extension O p B hB _ _ _ (Ch.step m (by omega) τ) k, Finset.sum_range_succ]
      abel
  rw [← hq0 τ]
  have h := hsum o le_rfl τ
  rw [hq o le_rfl τ, hper τ, Finset.sum_congr rfl (fun n hn => hl n (Finset.mem_range.1 hn) τ)] at h
  rw [sub_smul, one_smul]
  nth_rewrite 1 [h]
  abel

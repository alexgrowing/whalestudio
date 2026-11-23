import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference
import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepClosed
import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent
import Formalism.LogFactorialIndices.LogProductFormula

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

theorem finDim_of_isLat {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) (h : Formalism.LatticeIndexTer.IsLat O K V M) :
    FiniteDimensional K V := by
  obtain ⟨S, hS⟩ := h.1
  refine ⟨⟨S, ?_⟩⟩
  rw [← h.2, ← hS, Submodule.span_span_of_tower]

theorem qlen_inf_ne_top (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (M Θ : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M)
    (hΘ : Formalism.LatticeIndexTer.IsLat O K V Θ) (W : Submodule O V) :
    Formalism.LatticeIndexTer.qlen O V (M ⊓ W) (Θ ⊓ W) ≠ ⊤ := by
  have hfin := Formalism.LatticeIndexTer.latFinite O K V M Θ hM hΘ
  unfold Formalism.LatticeIndexTer.qlen at hfin ⊢
  let g : ↥(M ⊓ W) →ₗ[O] (↥M ⧸ Θ.comap M.subtype) :=
    (Θ.comap M.subtype).mkQ ∘ₗ Submodule.inclusion inf_le_left
  have hker : LinearMap.ker g = (Θ ⊓ W).comap (M ⊓ W).subtype := by
    ext ⟨y, hy⟩
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, hy.2⟩, fun h => h.1⟩
  have hle := Module.length_le_of_injective (g.ker.liftQ g le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
  rw [hker] at hle
  exact ne_top_of_le_ne_top hfin hle

theorem length_comap_eq {O V W : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W]
    [Module O W] (f : W →ₗ[O] V) (hf : Function.Injective f) (A B : Submodule O V)
    (hA : A ≤ LinearMap.range f) :
    Module.length O (↥(A.comap f) ⧸ (B.comap f).comap (A.comap f).subtype) =
      Module.length O (↥A ⧸ B.comap A.subtype) := by
  let g0 : ↥(A.comap f) →ₗ[O] ↥A := f.restrict (fun x hx => hx)
  have hg : Function.Bijective g0 := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hf
      exact congrArg Subtype.val hxy
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hA hy
      exact ⟨⟨x, hy⟩, rfl⟩
  let g : ↥(A.comap f) ≃ₗ[O] ↥A := LinearEquiv.ofBijective g0 hg
  refine (Submodule.Quotient.equiv _ _ g ?_).length_eq
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨x, hx⟩, hxB, hxy⟩
    have : f x = y := congrArg Subtype.val hxy
    simpa [← this] using hxB
  · intro hyB
    obtain ⟨x, rfl⟩ := hA hy
    exact ⟨⟨x, hy⟩, hyB, rfl⟩

theorem qlen_eq_zero_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (A B : Submodule O V)
    (h : B ≤ A) : Formalism.LatticeIndexTer.qlen O V B A = 0 := by
  unfold Formalism.LatticeIndexTer.qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    induction b using Submodule.Quotient.induction_on with
    | _ y => exact (Submodule.Quotient.eq _).2 (h (x - y).2)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem idx_bound (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (e : ℕ)
    (hH1 : H1 large₂ X H S wL nus) (hT : 1 ≤ T) (hcc : 0 ≤ cc D large₂ H.Cc H.Ac H.CRc wL)
    (hTe : (T : ℝ) * nus la ≤ (e : ℝ)) (L : LocDat X ka la) (hOk : L.Ok S wL wF T e)
    (U : Submodule (X.Kl la) ↥(WL X ka la)) :
    (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
              (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤
      (e : ℝ) * (finrank (X.Kl la) U : ℝ) + L.err T (cc D large₂ H.Cc H.Ac H.CRc wL) := by
  obtain ⟨⟨hMlat, hΘlat⟩, ⟨hbc, hϖ, hϖ'⟩, hTie, hRes, hPts, hLead⟩ := hOk
  have : FiniteDimensional (X.Kl la) ↥(WL X ka la) := finDim_of_isLat _ hMlat
  have hM₁ := Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt (X.Ol la) L.O' (X.Kl la) L.K' ↥(WL X ka la) L.V₁ L.bc hbc _ hMlat
  have hΘ₁ := Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt (X.Ol la) L.O' (X.Kl la) L.K' ↥(WL X ka la) L.V₁ L.bc hbc _ hΘlat
  have : FiniteDimensional L.K' L.V₁ := finDim_of_isLat _ hM₁
  have hν : ∀ z, L.ν z ≤ nus la + cc D large₂ H.Cc H.Ac H.CRc wL * L.v z := by
    intro z
    have h := hH1.2.2.2 la (L.y z)
    rw [(hTie z).1] at h
    exact EReal.coe_le_coe_iff.1 h
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := hRes
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hPts
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLead
  have key := Formalism.LatticeBaseChangeAlt.localStepClosed L.ι L.ep L.f L.ν L.v (nus la) (cc D large₂ H.Cc H.Ac H.CRc wL) T L.R L.I
    (fun z => (hTie z).2.2.1) hT hcc (fun z => (hTie z).2.2.2) hν L.O' L.K' L.K₁ L.V₁ L.Wsec
    (algebraMap (X.Ol la) L.O' L.ϖ) hϖ' (L.up (MW X ka la)) (L.up (ThW X S ka wL wF T la)) L.N₁ L.Z L.Zm L.N'
    e L.be L.n L.th L.c L.AA L.AA' L.N₁' L.ρ L.a L.a' hM₁ hΘ₁
    r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
    (Or.inl ⟨hTe, fun z => (hTie z).2.1⟩) L.Rr L.Aq L.xq L.nq L.Fq L.rq p1 p2 p3 p4 p5 p6 p7 p8
    L.A0 L.n1 L.F1 L.ι1 L.deg L.δ L.t L.σ L.u l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    (Submodule.span L.K' (L.bc '' (U : Set ↥(WL X ka la))))
  have hd : (0 : ℝ) < (finrank L.K' L.K₁ : ℝ) := by exact_mod_cast (finrank_pos : 0 < finrank L.K' L.K₁)
  have desc := Formalism.LatticeBaseChangeAlt.localStepDescent (X.Ol la) L.O' (X.Kl la) L.K' ↥(WL X ka la) L.V₁ L.bc hbc L.ϖ hϖ hϖ'
    (MW X ka la) (ThW X S ka wL wF T la) U hMlat hΘlat (finrank L.K' L.K₁ : ℝ)
    ((L.R : ℝ) * ((T : ℝ) * cc D large₂ H.Cc H.Ac H.CRc wL * ∑ z, ((L.ep z : ℝ) * L.f z) * L.v z) +
      (L.R : ℝ) * (L.I : ℝ) + ((Module.length L.O' (↥L.Zm ⧸ L.Z.comap L.Zm.subtype)).toNat : ℝ))
    (((IsDiscreteValuationRing.addVal L.O' L.a).toNat : ℝ) -
        ((IsDiscreteValuationRing.addVal L.O' L.a').toNat : ℝ) +
        (finrank L.K' L.K₁ : ℝ) * (L.n : ℝ) * (L.be : ℝ)) e
    (by
      refine le_trans key (le_of_eq ?_)
      ring)
  unfold LocDat.err
  rw [← mul_le_mul_iff_right₀ hd]
  refine le_trans desc (le_of_eq ?_)
  field_simp
  ring

theorem qlen_eq_inW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (N N' : Submodule (X.Ol la) (X.Vl la)) (V' : Submodule (X.Kl la) (X.Vl la))
    (hV' : V' ≤ WL X ka la) :
    Formalism.LatticeIndexTer.qlen (X.Ol la) ↥(WL X ka la)
              (inW X ka la N ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
              (inW X ka la N' ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la)) =
      X.qlen la (N ⊓ X.ofK la V') (N' ⊓ X.ofK la V') := by
  refine length_comap_eq ((WL X ka la).subtype.restrictScalars (X.Ol la)) ?_ (N ⊓ X.ofK la V')
    (N' ⊓ X.ofK la V') ?_
  · exact Subtype.val_injective
  · intro x hx
    exact ⟨⟨x, hV' hx.2⟩, rfl⟩

theorem thm0Local : @Thm0Local D B P j := by
  intro large₂ X H S ka wL wF T nus la e hH1 hT hcc hΘM hTe L hOk V' hV'
  have hb := idx_bound large₂ X H S ka wL wF T nus la e hH1 hT hcc hTe L hOk
    (V'.comap (WL X ka la).subtype)
  have hrk : finrank (X.Kl la) ↥(V'.comap (WL X ka la).subtype) = finrank (X.Kl la) V' :=
    (Submodule.comapSubtypeEquivOfLe hV').finrank_eq
  have hq := qlen_eq_inW X ka la (X.loc la (X.Msup ka)) (X.loc la (X.Theta S ka wL wF T)) V' hV'
  have hle : ThW X S ka wL wF T la ≤ MW X ka la :=
    Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘM))
  have h0 := qlen_eq_zero_of_le
    (MW X ka la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (ThW X S ka wL wF T la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (inf_le_inf_right _ hle)
  have hfin := qlen_inf_ne_top (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) (ThW X S ka wL wF T la)
    hOk.1.1 hOk.1.2 ((V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
  rw [← hq]
  refine ⟨hfin, ?_⟩
  rw [hrk] at hb
  unfold Formalism.LatticeIndexTer.idx at hb
  rw [h0] at hb
  have hb' := hb
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, Int.cast_natCast] at hb'
  exact hb'

end Formalism.MainNotions.Gaps.T0

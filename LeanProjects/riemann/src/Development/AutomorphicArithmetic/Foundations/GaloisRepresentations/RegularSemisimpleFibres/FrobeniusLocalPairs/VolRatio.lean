import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.VolIdx
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem mem_diag (g : GL (Fin n) k) :
    g ∈ (diagT k (Fin n)).range ↔ ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ i j hij
    rw [val_diagT, diagonal_apply_ne _ hij]
  · intro h
    have hd : (g : Matrix (Fin n) (Fin n) k) = diagonal fun i => (g : Matrix (Fin n) (Fin n) k) i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij, h i j hij]
    have hdet : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
    have hne : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
      intro i
      rw [hd, det_diagonal] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
    refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
    ext : 1
    rw [val_diagT]
    simp only [Units.val_mk0]
    exact hd.symm

private theorem isClosed_diag : IsClosed ((diagT k (Fin n)).range : Set (GL (Fin n) k)) := by
  haveI := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k
  have he : ((diagT k (Fin n)).range : Set (GL (Fin n) k)) =
      Units.val ⁻¹' {M : Matrix (Fin n) (Fin n) k | ∀ i j, i ≠ j → M i j = 0} := by
    ext g
    exact mem_diag g
  rw [he]
  refine IsClosed.preimage Units.continuous_val ?_
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_refl (g : GL (Fin n) k) : sg (RingEquiv.refl k) g = g := by
  ext i j
  simp [sg]

private theorem cent_diag {γ y : GL (Fin n) k} {x : Fin n → kˣ} (hx : Strict x)
    (hy : y⁻¹ * γ * y = diagT k (Fin n) x) {t : GL (Fin n) k} (ht : t ∈ Subgroup.centralizer {γ}) :
    y⁻¹ * t * y ∈ (diagT k (Fin n)).range := by
  have hc : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
  have hcyc : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have hz : (y⁻¹ * t * y)⁻¹ * diagT k (Fin n) x * sg (RingEquiv.refl k) (y⁻¹ * t * y) =
      diagT k (Fin n) x := by
    rw [sg_refl, ← hy]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc γ t y, hc, mul_assoc t, inv_mul_cancel_left]
  obtain ⟨s, hs⟩ := strictNormal k n (RingEquiv.refl k) 1 hcyc x x hx hx _ hz
  exact ⟨s, hs.symm⟩

end

theorem UpperTheory.Gal.InertialTypesAlt.L.volRatio :
    UpperTheory.Gal.InertialTypesAlt.L.VolRatio := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ r r' hr0 hr1 hr0' hr1' hrr'
  haveI : T2Space k := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k
  have hemb : Topology.IsClosedEmbedding (incl : GL (Fin n) k →* GL (Fin n) E) :=
    ((bridge k E σ).2.2 n).2.2.2.1
  obtain ⟨KE, hKE, -, -⟩ := ballSub E n r hr0 hr1
  obtain ⟨Kk, hKk, hKko, -⟩ := ballSub k n r' hr0' hr1'
  set D : Subgroup (GL (Fin n) k) := (diagT k (Fin n)).range with hD
  set Cr : Subgroup (GL (Fin n) k) := D ⊓ KE.comap (incl : GL (Fin n) k →* GL (Fin n) E) with hCr
  set Hr : Subgroup (GL (Fin n) k) := D ⊓ Kk with hHr
  have hincl : ∀ (g : GL (Fin n) k) (i j : Fin n),
      ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j) := by
    intro g i j
    rfl
  have hHC : Hr ≤ Cr := by
    rintro d ⟨⟨s, rfl⟩, hd⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    have hd' : diagT k (Fin n) s ∈ ball n r' := by
      rw [← hKk]
      exact hd
    show incl (diagT k (Fin n) s) ∈ KE
    rw [← SetLike.mem_coe, hKE]
    intro i j
    rw [hincl, val_diagT]
    by_cases hij : i = j
    · subst hij
      have h1 := hd' i i
      rw [val_diagT] at h1
      simpa using hrr' (s i) (by simpa using h1)
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hCrc : IsCompact (Cr : Set (GL (Fin n) k)) := by
    have h1 : IsCompact ((incl : GL (Fin n) k →* GL (Fin n) E) ⁻¹' (KE : Set (GL (Fin n) E))) :=
      hemb.isCompact_preimage (by rw [hKE]; exact BallG.isCompact_ball hr1)
    exact h1.inter_left isClosed_diag
  have hidx : Hr.relIndex Cr ≠ 0 := by
    haveI : CompactSpace Cr := isCompact_iff_compactSpace.mp hCrc
    have hopen : IsOpen ((Hr.subgroupOf Cr : Subgroup Cr) : Set Cr) := by
      have he : ((Hr.subgroupOf Cr : Subgroup Cr) : Set Cr) = Subtype.val ⁻¹' (Kk : Set (GL (Fin n) k)) := by
        ext g
        simp only [Subgroup.coe_subgroupOf, Set.mem_preimage, SetLike.mem_coe]
        exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
      rw [he]
      exact continuous_subtype_val.isOpen_preimage _ hKko
    haveI := Subgroup.quotient_finite_of_isOpen _ hopen
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨(Hr.relIndex Cr : ℝ), Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx), ?_⟩
  intro γ y x hx hy ν hν
  let c : GL (Fin n) k →* GL (Fin n) k :=
    { toFun := fun g => y⁻¹ * g * y
      map_one' := by simp
      map_mul' := by
        intro a b
        group }
  have hcs : Function.Surjective c := fun g => ⟨y * g * y⁻¹, by simp [c, mul_assoc]⟩
  set C : Subgroup (GL (Fin n) k) := Cr.comap c with hC
  set H : Subgroup (GL (Fin n) k) := Hr.comap c with hH
  have hTc : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    Set.isClosed_centralizer _
  have hCT : C ≤ Subgroup.centralizer {γ} := by
    intro g hg
    obtain ⟨s, hs⟩ := hg.1
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    have hγ : h = y * diagT k (Fin n) x * y⁻¹ := by
      rw [← hy]
      group
    have hg' : g = y * diagT k (Fin n) s * y⁻¹ := by
      rw [hs]
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]
      group
    rw [hγ, hg']
    simp only [mul_assoc, inv_mul_cancel_left]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]
  have hCc : IsCompact (C : Set (GL (Fin n) k)) :=
    ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage.2 hCrc
  have hcD : ∀ t : Subgroup.centralizer {γ}, c t ∈ D := fun t => cent_diag hx hy t.2
  have hHo : IsOpen {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} := by
    have he : {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} =
        (fun t : Subgroup.centralizer {γ} => y⁻¹ * (t : GL (Fin n) k) * y) ⁻¹' (Kk : Set (GL (Fin n) k)) := by
      ext t
      exact ⟨fun h => h.2, fun h => ⟨hcD t, h⟩⟩
    rw [he]
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).isOpen_preimage _ hKko
  have hv := (volIdx (GL (Fin n) k) (Subgroup.centralizer {γ}) C H hTc ν hν hCT hCc
    (Subgroup.comap_mono hHC) hHo).2
  have hri : H.relIndex C = Hr.relIndex Cr := by
    rw [hH, hC, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcs]
  have e1 : {t : Subgroup.centralizer {γ} | incl (y⁻¹ * (t : GL (Fin n) k) * y) ∈ ball n r} =
      {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ C} := by
    ext t
    show _ ↔ c t ∈ D ∧ incl (c t) ∈ KE
    rw [← SetLike.mem_coe (p := KE), hKE]
    exact ⟨fun h => ⟨hcD t, h⟩, fun h => h.2⟩
  have e2 : {t : Subgroup.centralizer {γ} | y⁻¹ * (t : GL (Fin n) k) * y ∈ ball n r'} =
      {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} := by
    ext t
    show _ ↔ c t ∈ D ∧ c t ∈ Kk
    rw [← SetLike.mem_coe (p := Kk), hKk]
    exact ⟨fun h => ⟨hcD t, h⟩, fun h => h.2⟩
  rw [e1, e2, hv, hri]

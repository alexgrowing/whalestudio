import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsExtra
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.WMem

theorem exists_rep {E W : Type} [Field E] [StarRing E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : W →ₗ⋆[E] W →ₗ[E] E) (han : ∀ x, h x x = 0 → x = 0)
    (U : Submodule E W) (f : W →ₗ⋆[E] E) : ∃ w ∈ U, ∀ σ ∈ U, f σ = h σ w := by
  let b := Module.finBasis E U
  let L : U →ₗ[E] (Fin (finrank E U) → E) := LinearMap.pi fun i => (h (b i : W)).comp U.subtype
  have key : ∀ (g g' : W →ₗ⋆[E] E), (∀ i, g (b i : W) = g' (b i : W)) → ∀ σ ∈ U, g σ = g' σ := by
    intro g g' hg σ hσ
    have : g.comp U.subtype = g'.comp U.subtype := b.ext fun i => hg i
    exact LinearMap.congr_fun this ⟨σ, hσ⟩
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 := key (h.flip (w : W)) 0 (fun i => by simpa [L] using congrFun hw i) w w.2
    exact Subtype.ext (han _ (by simpa using h0))
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨w, hw⟩ := hsurj fun i => f (b i : W)
  refine ⟨w, w.2, fun σ hσ => ?_⟩
  have := key f (h.flip (w : W)) (fun i => by simpa [L] using (congrFun hw i).symm) σ hσ
  simpa using this

theorem exists_smul_mem {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W) (v : W)
    (hv : v ∈ Submodule.span E (L : Set W)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.ClearingDenominatorsInOrder.main
  | exact _root_.GlobalTheory.ClearingDenominatorsInOrder.main
  | (apply _root_.GlobalTheory.ClearingDenominatorsInOrder.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearingDenominatorsInOrder.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearingDenominatorsInOrder.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearingDenominatorsInOrder.main ..)

theorem mem_perpE (D : D7) (P : LatW D) (v : (D.sp.X 0).V) :
    v ∈ perpE D P ↔ ∀ p ∈ P, (D.sp.X 0).hT p v = 0 := by
  simp [perpE, Submodule.mem_iInf]

theorem mem_orth {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ p ∈ U, S.hT p v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem hT_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (x y : S.V) : S.hT y x = star (S.hT x y) := by
  have := S.herm.eq x y
  rw [← this, starRingEnd_apply]

theorem hT_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [hT_symm, h, star_zero]

theorem hT_span {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    {s : Set S.V} {x y : S.V} (hx : x ∈ Submodule.span E s) (h : ∀ v ∈ s, S.hT v y = 0) :
    S.hT x y = 0 := by
  have : Submodule.span E s ≤ LinearMap.ker (S.hT y) :=
    Submodule.span_le.2 fun v hv => hT_zero S (h v hv)
  exact hT_zero S (this hx)

theorem eq_zero_of_dual {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    {r : ℕ} (e f : Fin r → S.V) (hef : ∀ i j, S.hT (e i) (f j) = if i = j then 1 else 0) {y : S.V}
    (hy : y ∈ Submodule.span E (Set.range f)) (h : ∀ i, S.hT (e i) y = 0) : y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
  have : ∀ i, c i = 0 := fun i => by simpa [map_sum, hef] using h i
  simp [this]

theorem iXY_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D)
    (he : F0.e = D.sp.hypE) (hs : IsSplit D F0 Λ) (σ : (D.sp.X 0).V)
    (hσ : σ ∈ L0X D Λ (lf D F0)) : D.sp.iXY 0 σ ∈ Λ := by
  have h1 : D.sp.iXY 0 σ ∈ Lrep Λ (lf D F0) ⊔ toO (hS D) (Xsp (lf D F0)) := hσ.1.1
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 h1
  have hX : Xsp (lf D F0) = Submodule.span D.host.E (Set.range D.sp.hypE) := by
    rw [← he]; rfl
  have hl1 : l ∈ XS D F0 ⊔ (Λ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs ▸ hl.1
  obtain ⟨l', hl', y, hy, rfl⟩ := Submodule.mem_sup.1 hl1
  obtain ⟨xs, hxs, m, hm, rfl⟩ := Submodule.mem_sup.1 hl'
  have hxs' : xs ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
    have : XS D F0 ≤ toO (hS D) (Submodule.span D.host.E (Set.range D.sp.hypE)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, c, -, rfl⟩
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, by rw [he]⟩)
    exact this hxs
  have hy' : y ∈ Submodule.span D.host.E (Set.range D.sp.hypF) := by
    have : YS D ≤ toO (hS D) (Submodule.span D.host.E (Set.range D.sp.hypF)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, c, -, rfl⟩
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)
    exact this hy
  have hx' : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := hX ▸ hx
  have hm' := (mem_orth (hS D) _ m).1 hm.2
  have hmE : ∀ i, (hS D).hT (D.sp.hypE i) m = 0 := fun i =>
    hm' _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  have hmF : ∀ i, (hS D).hT (D.sp.hypF i) m = 0 := fun i =>
    hm' _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  have hl2 := (mem_orth (hS D) _ _).1 hl.2
  have hy0 : y = 0 := by
    refine eq_zero_of_dual (hS D) _ _ D.sp.hyp_ef hy' fun i => ?_
    have h2 := hl2 (D.sp.hypE i) (by rw [hX]; exact Submodule.subset_span ⟨i, rfl⟩)
    have h3 : (hS D).hT (D.sp.hypE i) xs = 0 :=
      hT_zero _ (hT_span _ hxs' (by rintro _ ⟨j, rfl⟩; exact D.sp.hyp_ee j i))
    rwa [map_add, map_add, h3, hmE, zero_add, zero_add] at h2
  have hx0 : xs + x = 0 := by
    refine eq_zero_of_dual (hS D) D.sp.hypF D.sp.hypE (fun i j => ?_) (add_mem hxs' hx') fun i => ?_
    · rw [hT_symm, D.sp.hyp_ef]; by_cases hij : i = j <;> simp [hij, eq_comm]
    · have : xs + x = D.sp.iXY 0 σ - m := by rw [← hlx, hy0]; abel
      rw [this, map_sub, hmF, hT_zero _ (D.sp.hyp_orthX i σ).2, sub_zero]
  have : D.sp.iXY 0 σ = m := by
    rw [← hlx, hy0, show xs + m + 0 + x = (xs + x) + m by abel, hx0, zero_add]
  rw [this]; exact hm.1

theorem mem_dual {E W : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (h : W →ₗ⋆[E] W →ₗ[E] E) (L : Submodule (𝓞 E) W) (v : W) :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 E) E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem fvec_gram {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : FlagG S r T) (a b : Fin (r + 1)) :
    S.hT (F.fvec b) (F.fvec a) = if a = Fin.last r ∧ b = Fin.last r then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast j => simp [FlagG.fvec, F.z_orth, (Fin.castSucc_lt_last j).ne]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, hT_zero S (F.z_orth i), (Fin.castSucc_lt_last i).ne]
    | cast j => simp [FlagG.fvec, F.e_iso, (Fin.castSucc_lt_last i).ne]

theorem norm_cof {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hT : T ≠ 0) (x w : S.V) (ζ : E)
    (hx : x ∈ F.X) (hw : ∀ a, S.hT (F.fvec a) w = 0)
    (hom : ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec ((Zhat F F').submatrix Fin.castSucc id) b • F'.fvec b
      = x + w + ζ • F.z) :
    T * S.hT w w = leadMinorE (Zhat F F') (r + 1) * star (leadMinorE (Zhat F F') (r + 1)) -
      T * T' * (leadMinorE (Zhat F F') r * star (leadMinorE (Zhat F F') r)) := by
  have hZ : Formalism.HermitianLatticeCounting.LatticeSumBounds.crossGram S.hT.flip F.fvec F'.fvec = Zhat F F' := rfl
  have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.omegaNorm E S.V S.hT.flip (fun x y => hT_symm S y x) r F.fvec F'.fvec T T'
    (((-1 : E) ^ r) • x) (((-1 : E) ^ r) • w) ((-1 : E) ^ r * ζ) (fun a b => fvec_gram F a b)
    (fun a b => fvec_gram F' a b) hT
    (Submodule.smul_mem _ _ (by simpa [FlagG.fvec, FlagG.X] using (show x ∈ Submodule.span E (Set.range fun a => F.e a) from hx)))
    (fun a => by simp [hw a])
    (by
      rw [hZ]
      simp only [Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cofVecAdjugate E r (Zhat F F'), mul_smul]
      rw [← Finset.smul_sum, hom, smul_add, smul_add]
      simp [FlagG.fvec])
  rw [hZ] at h
  have h1 : leadMinorE (Zhat F F') (r + 1) = (Zhat F F').det := by
    simp [leadMinorE]
  have h2 : leadMinorE (Zhat F F') r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
    simp only [leadMinorE, dif_pos (Nat.le_succ r)]; rfl
  rw [h1, h2, ← h]
  have h3 : ((-1 : E) ^ r) * (-1) ^ r = 1 := by rw [← mul_pow]; simp
  simp only [LinearMap.flip_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    map_pow, map_neg, map_one]
  rw [← mul_assoc ((-1 : E) ^ r), h3, one_mul]

theorem main : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → P ≤ L0X D Λ (lf D F0) → ∀ F' ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∃ w : Fin (D.R.rS + 1) → (D.sp.X 0).V, (∀ b, IsWcomp D P (frame F' b) (w b) ∧ w b ∈ dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P)) ∧ ((Tu D u : ℕ) : D.host.E) * (D.sp.X 0).hT (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) = Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z := by
  intro D u u' F0 Λ hst hb hrow hsp P φ Z hφ hP F' hF'
  obtain ⟨hW, -, hpos, hlat, -, -, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hst hb hrow
  obtain ⟨hlift, he', hZ, horth⟩ := hF'
  have hiso := D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)
  have han : ∀ x, (D.sp.X 0).hT x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    have := hpos τ x h0
    simp [hx] at this
  have hex : ∀ b, ∃ w, IsWcomp D P (frame F' b) w := fun b => by
    obtain ⟨w, hw, hw'⟩ := exists_rep (D.sp.X 0).hT han (perpE D P)
      (((hS D).hT.flip (frame F' b)).comp (D.sp.iXY 0))
    exact ⟨w, hw, hw'⟩
  choose w hw using hex
  have hfΛ : ∀ b, frame F' b ∈ Λ := fun b => by
    induction b using Fin.lastCases with
    | last => simpa [FlagG.fvec] using hlift.1
    | cast j => simpa [FlagG.fvec] using he' j
  refine ⟨w, fun b => ⟨hw b, ?_, ?_⟩, ?_⟩
  · refine (mem_dual _ _ _).2 fun σ hσ => ?_
    rw [← (hw b).2 σ hσ.2]
    have huni : Formalism.HermitianLatticesTheory.dual (hS D).hT Λ = Λ := hrow.2.1.2.1
    exact (mem_dual _ _ _).1 (huni.symm ▸ hfΛ b) _ (iXY_mem D F0 Λ hb.1 hsp σ hσ.1)
  · obtain ⟨c, hc, hcw⟩ := exists_smul_mem (L0X D Λ (lf D F0)) (w b)
      (by rw [hlat.span_eq_top]; trivial)
    have hc1 : algebraMap (𝓞 D.host.E) D.host.E c ≠ 0 := by simpa using hc
    have hm : c • w b ∈ perpW D (L0X D Λ (lf D F0)) P :=
      ⟨hcw, ((perpE D P).restrictScalars (𝓞 D.host.E)).smul_mem c (hw b).1⟩
    have := Submodule.smul_mem (Submodule.span D.host.E
      (perpW D (L0X D Λ (lf D F0)) P : Set (D.sp.X 0).V)) (algebraMap (𝓞 D.host.E) D.host.E c)⁻¹
      (Submodule.subset_span hm)
    rw [← algebraMap_smul D.host.E c, smul_smul, inv_mul_cancel₀ hc1, one_smul] at this
    exact this
  · have hZ' : Zhat F0 F'.fl = Z := hZ
    subst hZ'
    set κ := Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec ((Zhat F0 F'.fl).submatrix Fin.castSucc id) with hκ
    set om : (hS D).V := ∑ b, κ b • F'.fl.fvec b with hom
    have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
      have := hst.2.2.2.1
      exact Nat.cast_ne_zero.2 (by omega)
    have hE : ∀ a, (hS D).hT (F0.e a) om = 0 := fun a => by
      have h := congrFun (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.kernelRowSpace _ _
        ((Zhat F0 F'.fl).submatrix Fin.castSucc id)).1 a
      rw [hom, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [← hκ] at h
      simpa [Matrix.mulVec, dotProduct, Zhat, brS, FlagG.fvec, mul_comm] using h
    have hXom : ∀ x ∈ F0.X, (hS D).hT x om = 0 := fun x hx =>
      hT_span _ hx (by rintro _ ⟨a, rfl⟩; exact hE a)
    have hXz : ∀ x ∈ F0.X, (hS D).hT x F0.z = 0 := fun x hx =>
      hT_span _ hx (by rintro _ ⟨a, rfl⟩; exact F0.z_orth a)
    set ζ : D.host.E := -((hS D).hT F0.z om) / ((Tu D u : ℕ) : D.host.E) with hζ
    have hperp : om - ζ • F0.z ∈ orth (hS D) (Xplus (lf D F0)) := by
      refine (mem_orth _ _ _).2 fun v hv => ?_
      obtain ⟨x, hx, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
      have h1 : (hS D).hT x (om - ζ • F0.z) = 0 := by
        rw [map_sub, map_smul, hXom x hx, hXz x hx]; simp
      have h2 : (hS D).hT t (om - ζ • F0.z) = 0 := by
        refine hT_span _ ht ?_
        rintro _ rfl
        rw [map_sub, map_smul, F0.z_norm, hζ, smul_eq_mul]
        field_simp
        ring
      rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    rw [← hW.1] at hperp
    obtain ⟨_, ⟨y, rfl⟩, x, hx, hyx⟩ := Submodule.mem_sup.1 hperp
    have hWp : ∀ (σ : (D.sp.X 0).V), ∀ v ∈ Xplus (lf D F0), (hS D).hT v (D.sp.iXY 0 σ) = 0 := fun σ =>
      (mem_orth _ _ _).1 (by rw [← hW.1]; exact Submodule.mem_sup_left ⟨σ, rfl⟩)
    have hzp : F0.z ∈ Xplus (lf D F0) := Submodule.mem_sup_right (Submodule.subset_span rfl)
    have hdec : om = x + D.sp.iXY 0 y + ζ • F0.z := by
      rw [add_comm x, hyx]; abel
    have hσom : ∀ σ, (hS D).hT (D.sp.iXY 0 σ) om = (D.sp.X 0).hT σ y := fun σ => by
      rw [hdec, map_add, map_add, map_smul, hT_zero _ (hWp σ x (Submodule.mem_sup_left hx)),
        hT_zero _ (hWp σ _ hzp), hiso]
      simp
    have hyP : y ∈ perpE D P := by
      refine (mem_perpE D P y).2 fun p hp => ?_
      have h1 : (hS D).hT (D.sp.iXY 0 p + φ ⟨p, hp⟩) om = 0 := by
        rw [hom, map_sum]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [map_smul, horth ⟨p, hp⟩ b, smul_zero]
      rwa [map_add, LinearMap.add_apply, hXom _ (hφ ⟨p, hp⟩).2, add_zero, hσom] at h1
    have hy : y = ∑ b, κ b • w b := by
      have hd : y - ∑ b, κ b • w b ∈ perpE D P :=
        sub_mem hyP (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hw b).1)
      refine sub_eq_zero.1 (han _ ?_)
      have h1 : ∀ σ ∈ perpE D P, (D.sp.X 0).hT σ (y - ∑ b, κ b • w b) = 0 := fun σ hσ => by
        rw [map_sub, ← hσom, hom, map_sum, map_sum, sub_eq_zero]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, map_smul, ← (hw b).2 σ hσ]
      exact h1 _ hd
    rw [← hy, ← hiso]
    refine norm_cof F0 F'.fl hT0 x (D.sp.iXY 0 y) ζ hx (fun a => hWp y _ ?_) hdec
    induction a using Fin.lastCases with
    | last => simpa [FlagG.fvec] using hzp
    | cast j =>
      have : F0.fvec j.castSucc = F0.e j := by simp [FlagG.fvec]
      rw [this]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.LoopC.WMem

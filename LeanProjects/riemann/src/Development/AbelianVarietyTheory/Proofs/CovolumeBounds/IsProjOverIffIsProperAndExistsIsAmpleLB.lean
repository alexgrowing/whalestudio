import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.AbLaw GlobalTheory.ProjSpace GlobalTheory.LBGerm

variable {X Y Z S : Scheme.{0}}

section Pull

variable {L : LB X}

theorem IsAmpleLB.pull_of_isImmersion_of_compactSpace (h : IsAmpleLB L) (f : Y ⟶ X) [IsImmersion f]
    [CompactSpace Y] : IsAmpleLB (L.pull f) := by
  refine ⟨LB.isLB_pull h.isLB f, inferInstance, fun y => ?_⟩
  obtain ⟨n, hn, s, hs, hle, ha⟩ := h.exists_affine_le (x := f y) (U := f.coborderRange)
    (subset_coborder ⟨y, rfl⟩)
  have e := nonzeroLocus_secPowPull s f
  refine ⟨n, hn, secPowPull s f, e.ge hs, ?_⟩
  have h₁ := (ha.preimage_of_isOpenImmersion f.coborderRange.ι
    (hle.trans f.coborderRange.opensRange_ι.ge)).preimage f.liftCoborder
  rwa [← Scheme.Hom.comp_preimage, f.liftCoborder_ι, ← e] at h₁

theorem IsAmpleLB.pull_of_isImmersion (h : IsAmpleLB L) (f : Y ⟶ X) [IsImmersion f] [QuasiCompact f] :
    IsAmpleLB (L.pull f) := by
  have := h.compactSpace
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  exact h.pull_of_isImmersion_of_compactSpace f

theorem IsAmpleLB.pull_of_isFinite (h : IsAmpleLB L) (f : Y ⟶ X) [IsFinite f] : IsAmpleLB (L.pull f) :=
  h.pull_of_isAffineHom f

theorem IsAmpleLB.pull_of_isClosedImmersion (h : IsAmpleLB L) (f : Y ⟶ X) [IsClosedImmersion f] :
    IsAmpleLB (L.pull f) :=
  h.pull_of_isAffineHom f

theorem IsAmpleLB.pull_of_isPullback (h : IsAmpleLB L) {S' : Scheme.{0}} {π : Y ⟶ X} {f' : Y ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (H : IsPullback π f' f g) [IsAffineHom g] : IsAmpleLB (L.pull π) := by
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  exact h.pull_of_isAffineHom π

theorem isAmpleLB_congr {M : LB X} (hL : L.IsLB) (hM : M.IsLB) (H : LBIso L M) : IsAmpleLB L ↔ IsAmpleLB M :=
  ⟨fun h => h.of_lbIso hM H.symm, fun h => h.of_lbIso hL H⟩

end Pull

section Tensor

variable {A B L M N : LB X}

theorem exists_sec_div_mul (hA : A.IsLB) (hB : B.IsLB) (t : (LB.div B A).Sec) (s : A.Sec) :
    ∃ u : B.Sec, ∀ (y : X) k l, y ∈ B.U k → y ∈ A.U l →
      gs (𝟙 X) y _ (u.f k) = gs (𝟙 X) y (B.U k ⊓ A.U l) (t.f (k, l)) * gs (𝟙 X) y _ (s.f l) := by
  have v : ∀ (y : X) (p : B.ι × A.ι), y ∈ B.U p.1 ⊓ A.U p.2 →
      gs (𝟙 X) y (B.U p.1 ⊓ A.U p.2) (@id Γ(X, B.U p.1 ⊓ A.U p.2) (t.f p) * resG X inf_le_right (s.f p.2)) =
        gs (𝟙 X) y (B.U p.1 ⊓ A.U p.2) (t.f p) * gs (𝟙 X) y _ (s.f p.2) := fun y p hy => by
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    rfl
  obtain ⟨u, hu⟩ := exists_sec_of_refinement hB (fun p : B.ι × A.ι => B.U p.1 ⊓ A.U p.2) Prod.fst
    (fun _ => inf_le_left)
    (fun y => (exists_chart hB y).elim fun k hk => (exists_chart hA y).elim fun l hl => ⟨(k, l), hk, hl⟩)
    (fun p => @id Γ(X, B.U p.1 ⊓ A.U p.2) (t.f p) * resG X inf_le_right (s.f p.2)) (fun y p q hp hq => by
      have e₁ : gs (𝟙 X) y (B.U p.1 ⊓ A.U p.2) (t.f p) = _ * gs (𝟙 X) y (B.U q.1 ⊓ A.U q.2) (t.f q) :=
        Segre.gs_compat t (𝟙 X) y (k := p) (k' := q) hp hq
      have e₂ := gm_div A B (𝟙 X) y p q ⟨hp, hq⟩
      rw [v y p hp, v y q hq, e₁, Segre.gs_compat s (𝟙 X) y hp.2 hq.2]
      erw [e₂]
      rw [Units.val_mul, mul_mul_mul_comm, mul_assoc (Units.val _), Units.inv_mul, mul_one])
  refine ⟨u, fun y k l hk hl => ?_⟩
  have e := hu y k (k, l) hk ⟨hk, hl⟩
  have c := gm_cocycle hB (𝟙 X) y hk hk hk
  rw [v y (k, l) ⟨hk, hl⟩, mul_eq_left.1 c, Units.val_one, one_mul] at e
  exact e

theorem exists_sec_nonzeroLocus_eq_inf_div (hA : A.IsLB) (hB : B.IsLB) (t : (LB.div B A).Sec) (s : A.Sec) :
    ∃ u : B.Sec, nonzeroLocus u = nonzeroLocus t ⊓ nonzeroLocus s := by
  obtain ⟨u, hu⟩ := exists_sec_div_mul hA hB t s
  refine ⟨u, nonzeroLocus_eq_of _ _ (fun y _ => exists_chart hB y) fun y k hk => ?_⟩
  obtain ⟨l, hl⟩ := exists_chart hA y
  rw [hu y k l hk hl, IsUnit.mul_iff]
  exact and_congr (mem_nonzeroLocus_iff_isUnit t (k := (k, l)) ⟨hk, hl⟩).symm
    (mem_nonzeroLocus_iff_isUnit s hl).symm

theorem exists_secMaps (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) (s : A.Sec) :
    ∃ u : B.Sec, SecMaps w s u := by
  obtain ⟨u, hu⟩ := exists_sec_div_mul hA hB (DVR.genSec w hw) s
  refine ⟨u, fun p => fn_ext fun y hy => ?_⟩
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy]
  exact hu y p.1 p.2 hy.1 hy.2

def chartPullDivPow (A B : LB X) (n : ℕ) :
    ChartPull (LB.div (lbPow B n) (lbPow A n)) (lbPow (LB.div B A) n) (𝟙 X) where
  idx p := fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)
  le _ _ hy := mem_powChart.2 ⟨mem_powChart.1 hy.1, mem_powChart.1 hy.2⟩
  g y p q hp hq := by
    have hp' : y ∈ B.U (p.1 PUnit.unit) ⊓ A.U (p.2 PUnit.unit) := ⟨mem_powChart.1 hp.1, mem_powChart.1 hp.2⟩
    have hq' : y ∈ B.U (q.1 PUnit.unit) ⊓ A.U (q.2 PUnit.unit) := ⟨mem_powChart.1 hq.1, mem_powChart.1 hq.2⟩
    refine (gm_div (lbPow A n) (lbPow B n) (𝟙 X) y p q ⟨hp, hq⟩).trans (Eq.trans ?_
      (gm_lbPow_g (L := LB.div B A) n (𝟙 X) y (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))
        (fun _ => (q.1 PUnit.unit, q.2 PUnit.unit)) (mem_powChart.2 hp') (mem_powChart.2 hq')).symm)
    rw [gm_lbPow_g n (𝟙 X) y _ _ hp.1 hq.1, gm_lbPow_g n (𝟙 X) y _ _ hp.2 hq.2, ← inv_pow, ← mul_pow]
    exact congrArg (· ^ n) (gm_div A B (𝟙 X) y (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit)
      ⟨hp', hq'⟩).symm

theorem exists_sec_pow_nonzeroLocus_eq_inf (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso M (LB.div N L))
    {n : ℕ} (s : (lbPow L n).Sec) (t : (lbPow M n).Sec) :
    ∃ u : (lbPow N n).Sec, nonzeroLocus u = nonzeroLocus t ⊓ nonzeroLocus s := by
  obtain ⟨t', ht'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow (LB.isLB_div hN hL) n) (isLB_lbPow hM n)
    (lbIso_lbPow H n).symm t
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_inf_div (isLB_lbPow hL n) (isLB_lbPow hN n)
    (chartSec (chartPullDivPow L N n) t') s
  refine ⟨u, ?_⟩
  rw [hu, nonzeroLocus_chartSec_id _ _ fun y _ _ =>
    exists_chart (LB.isLB_div (isLB_lbPow hN n) (isLB_lbPow hL n)) y, ht']

theorem IsAmpleLB.tensor_isGenerated (hL : IsAmpleLB L) (hM : IsGenerated M) (hN : N.IsLB)
    (H : ∃ t : (LB.div (LB.div N L) M).Gen, t.IsGen) : IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨t, ht⟩ := (hM.pow n).exists_mem x
  obtain ⟨u, hu⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hM.isLB hN H s t
  exact ⟨n, hn, u, hu.ge ⟨ht, hs⟩, hu ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hM.isLB n) t ha⟩

theorem IsAmpleLB.tensor (hL : IsAmpleLB L) (hM : IsAmpleLB M) (hN : N.IsLB)
    (H : ∃ t : (LB.div (LB.div N L) M).Gen, t.IsGen) : IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨m, hm, t, ht, -⟩ := hM.exists_affine x
  obtain ⟨u, hu⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hM.isLB hN H (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow t n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hu
  exact ⟨n * m, Nat.mul_pos hn hm, u, hu.ge ⟨ht, hs⟩,
    hu ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hM.isLB m) t ha⟩

end Tensor

section Product

theorem IsAmpleLB.box {L : LB X} {M : LB Y} {N : LB Z} (hL : IsAmpleLB L) (hM : IsAmpleLB M) (hN : N.IsLB)
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (P : IsPullback p q f g) [S.IsSeparated]
    (H : ∃ t : (LB.div (LB.div N (L.pull p)) (M.pull q)).Gen, t.IsGen) : IsAmpleLB N := by
  have hq : QuasiCompact q := by
    have := hL.compactSpace
    have : QuasiCompact (f ≫ terminal.from S) := by
      rw [terminal.comp_from]
      exact (compactSpace_iff_quasiCompact X).1 this
    have : QuasiCompact f := .of_comp f (terminal.from S)
    exact MorphismProperty.of_isPullback (P := @QuasiCompact) P this
  have := hM.compactSpace
  refine ⟨hN, QuasiCompact.compactSpace_of_compactSpace q, fun z => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine (p z)
  obtain ⟨m, hm, t, ht, hb⟩ := hM.exists_affine (q z)
  obtain ⟨u, hu⟩ := exists_sec_pow_nonzeroLocus_eq_inf (LB.isLB_pull hL.isLB p) (LB.isLB_pull hM.isLB q) hN H
    (secPowPull (secPow s m) p) (secPowPull (secCast (Nat.mul_comm m n) (secPow t n)) q)
  rw [nonzeroLocus_secPowPull, nonzeroLocus_secPowPull, nonzeroLocus_secCast, nonzeroLocus_secPow _ hn,
    nonzeroLocus_secPow _ hm] at hu
  refine ⟨n * m, Nat.mul_pos hn hm, u, hu.ge ⟨ht, hs⟩, ?_⟩
  have : IsAffine (nonzeroLocus s) := ha
  have : IsAffineHom (((nonzeroLocus s).ι ≫ f) ≫ terminal.from S) := inferInstance
  have h₁ : IsAffineHom ((nonzeroLocus s).ι ≫ f) := .of_comp _ (terminal.from S)
  have h₂ : IsAffineHom ((p ⁻¹ᵁ nonzeroLocus s).ι ≫ q) := MorphismProperty.of_isPullback (P := @IsAffineHom)
    ((isPullback_morphismRestrict p (nonzeroLocus s)).paste_vert P) h₁
  have h₃ := (hb.preimage ((p ⁻¹ᵁ nonzeroLocus s).ι ≫ q)).image_of_isOpenImmersion (p ⁻¹ᵁ nonzeroLocus s).ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_comm, ← hu] at h₃

theorem IsAmpleLB.linComb_of_isWideProduct [IsAffine S] {L : LB X} (hL : IsAmpleLB L) {j : ℕ} {π : X ⟶ S}
    {π' : Y ⟶ S} {ρ : Fin j → (Y ⟶ X)} (hw : Segre.IsWideProduct π' (fun _ => π) ρ) :
    IsAmpleLB (LB.LinComb L (K := Fin j) ρ (fun _ => 1)) := by
  obtain ⟨n, hn, N, s, hs, ha⟩ := hL.exists_cover
  have hB : (LB.LinComb L (K := Fin j) ρ (fun _ => 1)).IsLB := LB.isLB_linComb hL.isLB _ _
  have le : ∀ (k : (lbPow (LB.LinComb L (K := Fin j) ρ (fun _ => 1)) n).ι) (i : Fin j),
      (lbPow (LB.LinComb L (K := Fin j) ρ (fun _ => 1)) n).U k ≤
        ρ i ⁻¹ᵁ (lbPow L n).U (fun _ => k PUnit.unit i) := fun k i y hy =>
    mem_powChart.2 (Set.mem_iInter.1 (mem_powChart.1 hy) i)
  choose t ht using fun a : Fin j → Fin (N + 1) => Segre.exists_boxSec (P := lbPow L n)
    (P' := lbPow (LB.LinComb L (K := Fin j) ρ (fun _ => 1)) n)
    (idx := fun k i _ => k PUnit.unit i) le (fun y k k' hk hk' => by
      refine (gm_lbPow_g n (𝟙 Y) y k k' hk hk').trans ?_
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ =>
        (gm_lbPow_g n (ρ i) y _ _ (le k i hk) (le k' i hk')).symm)
      rw [Finset.prod_pow]
      refine congrArg (· ^ n) ((gm_linComb L ρ (fun _ => 1) (𝟙 Y) y _ _ (mem_powChart.1 hk)
        (mem_powChart.1 hk')).trans ?_)
      simp only [zpow_one, Category.id_comp]) (fun i => s (a i))
  have loc : ∀ a (y : Y), y ∈ nonzeroLocus (t a) ↔ ∀ i, ρ i y ∈ nonzeroLocus (s (a i)) := fun a y => by
    obtain ⟨k, hk⟩ := exists_chart (isLB_lbPow hB n) y
    rw [mem_nonzeroLocus_iff_isUnit (t a) hk, ht a k y hk, IsUnit.prod_univ_iff]
    exact forall_congr' fun i => (mem_nonzeroLocus_iff_pull _ _ _ (le k i hk)).symm
  refine isAmpleLB_of_cover hB hn t (top_le_iff.1 fun y _ => ?_) fun a => ?_
  · choose a ha using fun i => Opens.mem_iSup.1 (hs.ge (Set.mem_univ (ρ i y)))
    exact Opens.mem_iSup.2 ⟨a, (loc a y).2 ha⟩
  · exact (hw.affineOpen ⊤ (fun i => nonzeroLocus (s (a i))) (nonzeroLocus (t a)) (fun _ => le_top) le_top
      (fun i y hy => (loc a y).1 hy i) (fun y _ hy => (loc a y).2 hy) (isAffineOpen_top _) (fun i => ha _)).1

theorem isWideProduct_of_isLimit {G' G : Over S} {j : ℕ} {pr : Fin j → (G' ⟶ G)} (lim : IsLimit (Fan.mk G' pr)) :
    Segre.IsWideProduct G'.hom (fun _ => G.hom) (fun i => (pr i).left) := by
  refine ⟨fun i => Over.w _, fun Z z f hf => ?_⟩
  let c : Fan (fun _ : Fin j => G) := Fan.mk (Over.mk z) (fun i => Over.homMk (f i) (hf i))
  refine ⟨(lim.lift c).left, ⟨Over.w (lim.lift c), fun i =>
    congrArg (fun q => q.left) (lim.fac c ⟨i⟩)⟩, fun g hg => ?_⟩
  exact congrArg (fun q => q.left) (lim.uniq c (Over.homMk g hg.1) (fun i => Over.OverMorphism.ext (hg.2 i.as)))

theorem IsAmpleLB.boxLB [IsAffine S] {G' G : Over S} {j : ℕ} {pr : Fin j → (G' ⟶ G)}
    (lim : IsLimit (Fan.mk G' pr)) {L : LB G.left} (hL : IsAmpleLB L) : IsAmpleLB (boxLB L pr) :=
  hL.linComb_of_isWideProduct (isWideProduct_of_isLimit lim)

end Product

section Projective

variable {R : Type} [CommRing R] {L : LB X}

theorem isClosedImmersion_morphismRestrict_of_surjective (φ : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : φ ⁻¹ᵁ U = W) (h : Function.Surjective (φ.appLE U W e.ge).hom) :
    IsClosedImmersion (φ ∣_ U) := by
  subst e
  rw [← Scheme.Hom.app_eq_appLE] at h
  have : IsAffine U := hU
  have : IsAffine (φ ⁻¹ᵁ U) := hW
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk hW.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) :
      Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]
  exact IsClosedImmersion.spec_of_surjective _ h

theorem exists_generators (f : X ⟶ Sp R) [LocallyOfFiniteType f] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ (m : ℕ) (g : Fin m → Γ(X, W)), Function.Surjective (MvPolynomial.eval₂Hom (baseRingHom f W).hom g) := by
  have h : (baseRingHom f W).hom.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) hW le_top).comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)
  let _ : Algebra R Γ(X, W) := (baseRingHom f W).hom.toAlgebra
  obtain ⟨m, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine ⟨m, fun i => φ (MvPolynomial.X i), fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hφ a
  exact ⟨p, (MvPolynomial.aeval_unique φ ▸ rfl : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) p = φ p)⟩

theorem exists_sec_eq_fn_mul_pow [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {n : ℕ}
    (s : (lbPow L n).Sec) (g : Γ(X, nonzeroLocus s)) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∃ u : (lbPow L (n * k)).Sec, ∀ J,
      resG X (inf_le_right : nonzeroLocus s ⊓ (lbPow L (n * k)).U J ≤ _) (u.f J) =
        resG X inf_le_left g * resG X inf_le_right ((secPow s k).f J) := by
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 0) hL s (fun J => resG X inf_le_left g)
    (mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hs hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, one_mul]
      exact (gs_res (𝟙 X) y inf_le_left ⟨hs, hJ⟩ g).trans (gs_res (𝟙 X) y inf_le_left ⟨hs, hJ'⟩ g).symm)
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨u, hu⟩ := hN k hk
  exact ⟨secCast (Nat.zero_add _) u, fun J => (hu J).trans ((mul_comm _ _).trans
    (congrArg (_ * ·) (map_pow _ _ _).symm))⟩

theorem isImmersion_toProj (f : X ⟶ Sp R) {M : ℕ} (t : Fin (M + 1) → L.Sec) (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
    (H : ∀ x : X, ∃ (i : Fin (M + 1)) (W : X.Opens) (e : nonzeroLocus (t i) = W), x ∈ W ∧ IsAffineOpen W ∧
      ∃ (ι : Type) (a : ι → Fin (M + 1)), Function.Surjective (MvPolynomial.eval₂Hom (baseRingHom f W).hom
        fun j => resG X e.ge (secRatio (t i) (t (a j))))) :
    IsImmersion (toProj f t ht) := by
  choose i W e hx hW ι a hs using H
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have e' := fun x => (toProj_preimage_chart f t ht (i x)).trans (e x)
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (fun x => chart R M (i x)) ?_ fun x => ?_
  · rintro _ ⟨x, rfl⟩
    exact Opens.mem_iSup.2 ⟨x, (e' x).ge (hx x)⟩
  · have := isClosedImmersion_morphismRestrict_of_surjective (toProj f t ht) (isAffineOpen_chart R M (i x))
      (hW x) (e' x) ?_
    · infer_instance
    rw [surjective_appLE_chart_iff, toProj_str, funext fun j => pullRatio_toProj_on f t ht (i x) j (e' x).ge]
    intro b
    obtain ⟨p, rfl⟩ := hs x b
    exact ⟨MvPolynomial.rename (a x) p, MvPolynomial.eval₂_rename _ _ _ _⟩

theorem IsAmpleLB.exists_isImmersion_mul (h : IsAmpleLB L) (f : X ⟶ Sp R) [LocallyOfFiniteType f] :
    ∃ n, 1 ≤ n ∧ ∃ N, ∀ k, N ≤ k → ∃ (M : ℕ) (t : Fin (M + 1) → (lbPow L (n * k)).Sec)
      (ht : ⨆ i, nonzeroLocus (t i) = ⊤), IsImmersion (toProj f t ht) := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨n, hn, c, s, hs, ha⟩ := h.exists_cover
  choose m g hg using fun i => exists_generators f (ha i)
  choose N hN using fun p : Σ i, Fin (m i) => exists_sec_eq_fn_mul_pow h.isLB (s p.1) (g p.1 p.2)
  refine ⟨n, hn, Finset.univ.sup N + 1, fun k hk => ?_⟩
  have hk₁ : 1 ≤ k := le_trans (Nat.le_add_left _ _) hk
  choose u hu using fun p => hN p k ((Finset.le_sup (f := N) (Finset.mem_univ p)).trans (Nat.le_of_succ_le hk))
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero
    (Fintype.card_pos (α := Fin (c + 1) ⊕ Σ i, Fin (m i))).ne'
  obtain ⟨t, a, b, hta, htb⟩ : ∃ (t : Fin (M + 1) → (lbPow L (n * k)).Sec) (a : Fin (c + 1) → Fin (M + 1))
      (b : (Σ i, Fin (m i)) → Fin (M + 1)), (∀ i, t (a i) = secPow (s i) k) ∧ ∀ p, t (b p) = u p :=
    let e := Fintype.equivFinOfCardEq hM
    ⟨fun j => Sum.elim (fun i => secPow (s i) k) u (e.symm j), fun i => e (.inl i), fun p => e (.inr p),
      fun i => by simp only [e.symm_apply_apply, Sum.elim_inl], fun p => by
        simp only [e.symm_apply_apply, Sum.elim_inr]⟩
  have loc : ∀ i, nonzeroLocus (t (a i)) = nonzeroLocus (s i) := fun i => by
    rw [hta, nonzeroLocus_secPow _ hk₁]
  refine ⟨M, t, top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup_of_le (a i) (loc i).ge)),
    isImmersion_toProj f t _ fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
  refine ⟨a i, _, loc i, hi, ha i, Fin (m i), fun j => b ⟨i, j⟩, ?_⟩
  have e : g i = fun j => resG X (loc i).ge (secRatio (t (a i)) (t (b ⟨i, j⟩))) := funext fun j =>
    eq_resG_secRatio _ _ _ fun J => by rw [hta, htb]; exact hu ⟨i, j⟩ J
  exact e ▸ hg i

theorem IsAmpleLB.exists_isImmersion (h : IsAmpleLB L) (f : X ⟶ Sp R) [LocallyOfFiniteType f] :
    ∃ n, 1 ≤ n ∧ ∃ (M : ℕ) (t : Fin (M + 1) → (lbPow L n).Sec) (ht : ⨆ i, nonzeroLocus (t i) = ⊤),
      IsImmersion (toProj f t ht) := by
  obtain ⟨n, hn, N, H⟩ := h.exists_isImmersion_mul f
  exact ⟨n * (N + 1), Nat.mul_pos hn N.succ_pos, H _ N.le_succ⟩

theorem IsAmpleLB.isQProjOver (h : IsAmpleLB L) (f : X ⟶ Sp R) [LocallyOfFiniteType f] : IsQProjOver f := by
  obtain ⟨n, -, M, t, ht, H⟩ := h.exists_isImmersion f
  have := h.compactSpace
  have := isProper_str R M
  have : QuasiCompact (toProj f t ht ≫ PSpace.str R M) := inferInstance
  exact ⟨M, _, H, .of_comp _ (PSpace.str R M), toProj_str f t ht⟩

theorem isClosedImmersion_of_isProper {M : ℕ} (φ : X ⟶ PSpace R M) [IsImmersion φ]
    [IsProper (φ ≫ PSpace.str R M)] : IsClosedImmersion φ := by
  have := isProper_str R M
  have : IsProper φ := .of_comp φ (PSpace.str R M)
  exact .of_isPreimmersion φ φ.isClosedMap.isClosed_range

theorem IsAmpleLB.exists_veryAmpleBy_mul (h : IsAmpleLB L) (f : X ⟶ Sp R) [IsProper f] :
    ∃ n, 1 ≤ n ∧ ∃ N, ∀ k, N ≤ k → ∃ (M : ℕ) (t : Fin (M + 1) → (lbPow L (n * k)).Sec),
      VeryAmpleBy f (lbPow L (n * k)) t := by
  obtain ⟨n, hn, N, H⟩ := h.exists_isImmersion_mul f
  refine ⟨n, hn, N, fun k hk => ?_⟩
  obtain ⟨M, t, ht, H⟩ := H k hk
  have : IsProper (toProj f t ht ≫ PSpace.str R M) := by rwa [toProj_str]
  exact ⟨M, t, (veryAmpleBy_iff f t).2 ⟨ht, isClosedImmersion_of_isProper _⟩⟩

theorem IsAmpleLB.exists_veryAmpleBy (h : IsAmpleLB L) (f : X ⟶ Sp R) [IsProper f] :
    ∃ n, 1 ≤ n ∧ ∃ (M : ℕ) (t : Fin (M + 1) → (lbPow L n).Sec), VeryAmpleBy f (lbPow L n) t := by
  obtain ⟨n, hn, N, H⟩ := h.exists_veryAmpleBy_mul f
  exact ⟨n * (N + 1), Nat.mul_pos hn N.succ_pos, H _ N.le_succ⟩

theorem IsAmpleLB.isProjOver (h : IsAmpleLB L) (f : X ⟶ Sp R) [IsProper f] : IsProjOver f := by
  obtain ⟨_, -, _, _, H⟩ := h.exists_veryAmpleBy f
  exact isProjOver_of_veryAmpleBy H

theorem exists_isAmpleLB_of_isProjOver {f : X ⟶ Sp R} (h : IsProjOver f) : ∃ L : LB X, IsAmpleLB L := by
  obtain ⟨N, i, _, -⟩ := h
  exact ⟨_, (isAmple_projective_O_one R N).pull_of_isAffineHom i⟩

theorem isProjOver_iff_isProper_and_exists_isAmpleLB (f : X ⟶ Sp R) :
    IsProjOver f ↔ IsProper f ∧ ∃ L : LB X, IsAmpleLB L := by
  refine ⟨fun h => ⟨?_, exists_isAmpleLB_of_isProjOver h⟩, fun ⟨_, _, h⟩ => h.isProjOver f⟩
  obtain ⟨N, i, _, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem isProjOver_comp_of_isFinite (g : Y ⟶ X) [IsFinite g] {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProjOver (g ≫ f) := by
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 h
  exact (hL.pull_of_isFinite g).isProjOver _

theorem exists_veryAmpleBy_of_lbIso {f : X ⟶ Sp R} {B : LB X} (hL : L.IsLB) (hB : B.IsLB) (H : LBIso L B) {M : ℕ}
    {s : Fin (M + 1) → L.Sec} (h : VeryAmpleBy f L s) : ∃ t : Fin (M + 1) → B.Sec, VeryAmpleBy f B t := by
  obtain ⟨w, hw⟩ := H
  obtain ⟨hs, hc⟩ := (veryAmpleBy_iff f s).1 h
  choose t ht using fun i => exists_secMaps hL hB w hw (s i)
  refine ⟨t, (veryAmpleBy_iff f t).2 ⟨iSup_nonzeroLocus_of_secMaps hs hL hB ht, ?_⟩⟩
  rwa [toProj_eq_of_secMaps hs _ ht]

theorem isAmpleLB_of_veryAmpleBy {f : X ⟶ Sp R} {M : ℕ} {s : Fin (M + 1) → L.Sec} (h : VeryAmpleBy f L s) :
    IsAmpleLB L :=
  isAmpleLB_of_cover (IsGenerated.isLB ⟨_, s, h.1⟩) le_rfl (fun i => secToPow (s i) 1)
    (by simp only [nonzeroLocus_secToPow _ le_rfl, h.1])
    fun i => (nonzeroLocus_secToPow (s i) le_rfl).symm ▸ (h.2 i).1

theorem relAmple_of_isAmpleLB (A : Over S) [IsProper A.hom] {L : LB A.left} (hL : L.IsLB)
    (h : ∀ U : S.Opens, IsAffineOpen U → IsAmpleLB (L.pull (A.hom ⁻¹ᵁ U).ι)) : RelAmple A L := by
  intro U hU
  obtain ⟨n, hn, M, s, hs⟩ := (h U hU).exists_veryAmpleBy (R := Γ(S, U)) (A.hom ∣_ U ≫ hU.isoSpec.hom)
  obtain ⟨t, ht⟩ := exists_veryAmpleBy_of_lbIso (isLB_lbPow (LB.isLB_pull hL _) n) (LB.isLB_linComb hL _ _)
    (lbIso_lbPow_finPow hL (A.hom ⁻¹ᵁ U).ι n) hs
  exact ⟨n, hn, M, t, (veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom t).1 ht⟩

theorem relAmple_iff_isAmpleLB (A : Over S) [IsProper A.hom] {L : LB A.left} (hL : L.IsLB) :
    RelAmple A L ↔ ∀ U : S.Opens, IsAffineOpen U → IsAmpleLB (L.pull (A.hom ⁻¹ᵁ U).ι) :=
  ⟨isAmpleLB_of_relAmple A hL, relAmple_of_isAmpleLB A hL⟩

theorem relAmple_iff_isAmpleLB_of_isAffine [IsAffine S] (A : Over S) [IsProper A.hom] {L : LB A.left}
    (hL : L.IsLB) : RelAmple A L ↔ IsAmpleLB L :=
  ⟨isAmpleLB_of_relAmple_of_isAffine A hL, fun h => relAmple_of_isAmpleLB A hL fun U hU =>
    have : IsAffine U := hU
    h.pull_of_isPullback (isPullback_morphismRestrict A.hom U).flip (g := U.ι)⟩

end Projective

section Twist

variable {L M : LB X}

theorem exists_gen_div_div_tw (hL : L.IsLB) (hM : M.IsLB) :
    ∃ t : (LB.div (LB.div (tw L M 1) L) M).Gen, t.IsGen := by
  have l₁ : ∀ p : ((L.ι × M.ι) × L.ι) × M.ι,
      L.U p.1.1.1 ⊓ M.U p.1.1.2 ⊓ L.U p.1.2 ⊓ M.U p.2 ≤ L.U p.1.1.1 ⊓ L.U p.1.2 := fun p y hy => ⟨hy.1.1.1, hy.1.2⟩
  have l₂ : ∀ p : ((L.ι × M.ι) × L.ι) × M.ι,
      L.U p.1.1.1 ⊓ M.U p.1.1.2 ⊓ L.U p.1.2 ⊓ M.U p.2 ≤ M.U p.1.1.2 ⊓ M.U p.2 := fun p y hy => ⟨hy.1.1.2, hy.2⟩
  have v : ∀ (y : X) (p : ((L.ι × M.ι) × L.ι) × M.ι), y ∈ L.U p.1.1.1 ⊓ M.U p.1.1.2 ⊓ L.U p.1.2 ⊓ M.U p.2 →
      gm (𝟙 X) y _ (res (l₁ p) (L.g p.1.1.1 p.1.2) * res (l₂ p) (M.g p.1.1.2 p.2)) =
        gm (𝟙 X) y _ (L.g p.1.1.1 p.1.2) * gm (𝟙 X) y _ (M.g p.1.1.2 p.2) := fun y p hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
  refine ⟨⟨fun p => res (l₁ p) (L.g p.1.1.1 p.1.2) * res (l₂ p) (M.g p.1.1.2 p.2)⟩,
    fun p q => unit_ext fun y hy => ?_⟩
  have e₁ := gm_div M (LB.div (tw L M 1) L) (𝟙 X) y p q hy
  have e₂ := gm_div L (tw L M 1) (𝟙 X) y p.1 q.1 ⟨hy.1.1, hy.2.1⟩
  have hm : y ∈ L.U p.1.1.1 ⊓ M.U p.1.1.2 ⊓ (L.U q.1.1.1 ⊓ M.U q.1.1.2) := ⟨hy.1.1.1, hy.2.1.1⟩
  have e₃ : gm (𝟙 X) y _ ((tw L M 1).g p.1.1 q.1.1) =
      gm (𝟙 X) y _ (L.g p.1.1.1 q.1.1.1) * gm (𝟙 X) y _ (M.g p.1.1.2 q.1.1.2) :=
    (congrArg (gm (𝟙 X) y _) (tw_g L M 1 p.1.1 q.1.1)).trans (by
      rw [zpow_one]
      exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hm _) (gm_res (𝟙 X) y _ hm _)))
  refine ((gm_res (𝟙 X) y _ hy _).trans (v y p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (e₁.trans (congrArg (· * _) (e₂.trans (congrArg (· * _) e₃))))
      ((gm_res (𝟙 X) y _ hy _).trans (v y q hy.2))).trans ?_)))
  have a₁ := gm_cocycle hL (𝟙 X) y hy.1.1.1.1 hy.1.1.2 hy.2.1.2
  have a₂ := gm_cocycle hL (𝟙 X) y hy.1.1.1.1 hy.2.1.1.1 hy.2.1.2
  have b₁ := gm_cocycle hM (𝟙 X) y hy.1.1.1.2 hy.1.2 hy.2.2
  have b₂ := gm_cocycle hM (𝟙 X) y hy.1.1.1.2 hy.2.1.1.2 hy.2.2
  rw [eq_mul_inv_of_mul_eq (a₁.trans a₂.symm), eq_mul_inv_of_mul_eq (b₁.trans b₂.symm)]
  have key : ∀ {Γ : Type} [CommGroup Γ] (a b c d e f : Γ),
      a * b * c⁻¹ * d⁻¹ * (e * f) = a * e * c⁻¹ * (b * f * d⁻¹) := fun a b c d e f => by ac_rfl
  exact key _ _ _ _ _ _

theorem IsAmpleLB.tw_one (hL : IsAmpleLB L) (hM : IsGenerated M) : IsAmpleLB (tw L M 1) :=
  hL.tensor_isGenerated hM (isLB_tw hL.isLB hM.isLB 1) (exists_gen_div_div_tw hL.isLB hM.isLB)

end Twist

section Summary

attribute [local instance] Over.cartesianMonoidalCategory

theorem isProper_of_veryAmpleBy {R : Type} [CommRing R] {f : X ⟶ Sp R} {L : LB X} {M : ℕ}
    {s : Fin (M + 1) → L.Sec} (h : VeryAmpleBy f L s) : IsProper f :=
  ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 (isProjOver_of_veryAmpleBy h)).1

theorem relAmple_of_isAbelianScheme (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB)
    (h : ∀ U : S.Opens, IsAffineOpen U → IsAmpleLB (L.pull (A.hom ⁻¹ᵁ U).ι)) : RelAmple A L :=
  have := hA.proper
  relAmple_of_isAmpleLB A hL h

theorem isAmpleLB_basic :
    (∀ {X : Scheme.{0}} {L M : LB X}, L.IsLB → M.IsLB → LBIso L M → (IsAmpleLB L ↔ IsAmpleLB M)) ∧
    (∀ {X : Scheme.{0}} {L : LB X} {n : ℕ}, L.IsLB → 1 ≤ n → (IsAmpleLB (lbPow L n) ↔ IsAmpleLB L)) ∧
    (∀ {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X), IsAffineHom f → IsAmpleLB L → IsAmpleLB (L.pull f)) ∧
    (∀ {X Y S S' : Scheme.{0}} {L : LB X} {π : Y ⟶ X} {f' : Y ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S},
      IsPullback π f' f g → IsAffineHom g → IsAmpleLB L → IsAmpleLB (L.pull π)) ∧
    (∀ {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X), IsImmersion f → QuasiCompact f → IsAmpleLB L →
      IsAmpleLB (L.pull f)) ∧
    (∀ {X : Scheme.{0}} {L M N : LB X}, IsAmpleLB L → IsGenerated M → N.IsLB →
      (∃ t : (LB.div (LB.div N L) M).Gen, t.IsGen) → IsAmpleLB N) ∧
    (∀ (R : Type) [CommRing R] (N : ℕ), IsAmpleLB (O1 R N)) ∧
    (∀ {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X} (f : X ⟶ Sp R), LocallyOfFiniteType f → IsAmpleLB L →
      (∃ n, 1 ≤ n ∧ ∃ (M : ℕ) (t : Fin (M + 1) → (lbPow L n).Sec) (ht : ⨆ i, nonzeroLocus (t i) = ⊤),
        IsImmersion (toProj f t ht)) ∧ IsQProjOver f) ∧
    (∀ {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X} (f : X ⟶ Sp R), IsProper f → IsAmpleLB L →
      (∃ n, 1 ≤ n ∧ ∃ (M : ℕ) (t : Fin (M + 1) → (lbPow L n).Sec), VeryAmpleBy f (lbPow L n) t) ∧ IsProjOver f) ∧
    (∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}, IsAbelianScheme A → L.IsLB →
      (∀ U : S.Opens, IsAffineOpen U → IsAmpleLB (L.pull (A.hom ⁻¹ᵁ U).ι)) → RelAmple A L) ∧
    (∀ {R : Type} [CommRing R] {X Y : Scheme.{0}} (g : Y ⟶ X) (f : X ⟶ Sp R), IsFinite g → IsProjOver f →
      IsProjOver (g ≫ f)) ∧
    (∀ {X Y Z S : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S},
      IsPullback p q f g → S.IsSeparated → IsAmpleLB L → IsAmpleLB M → N.IsLB →
      (∃ t : (LB.div (LB.div N (L.pull p)) (M.pull q)).Gen, t.IsGen) → IsAmpleLB N) ∧
    (∀ {S : Scheme.{0}} {G' G : Over S} {j : ℕ} {pr : Fin j → (G' ⟶ G)} {L : LB G.left}, IsAffine S →
      IsLimit (Fan.mk G' pr) → IsAmpleLB L → IsAmpleLB (boxLB L pr)) :=
  ⟨isAmpleLB_congr, fun hL hn => isAmpleLB_pow_iff hL hn, fun f _ h => h.pull_of_isAffineHom f, fun H _ h => h.pull_of_isPullback H,
    fun f _ _ h => h.pull_of_isImmersion f, IsAmpleLB.tensor_isGenerated, isAmple_projective_O_one,
    fun f _ h => ⟨h.exists_isImmersion f, h.isQProjOver f⟩, fun f _ h => ⟨h.exists_veryAmpleBy f, h.isProjOver f⟩,
    fun A _ _ hA hL h => relAmple_of_isAbelianScheme A hA hL h, fun g _ _ h => isProjOver_comp_of_isFinite g h,
    fun P _ hL hM hN H => hL.box hM hN P H, fun _ lim h => h.boxLB lim⟩

example : IsAmpleLB (tw (O1 ℚ 2) (O1 ℚ 2) 1) := (isAmple_projective_O_one ℚ 2).tw_one (isGenerated_O1 ℚ 2)

example (R : Type) [CommRing R] (m n : ℕ) :
    IsProjOver (pullback.fst (PSpace.str R m) (PSpace.str R n) ≫ PSpace.str R m) := by
  have := isProper_str R m
  have := isProper_str R n
  have hL := LB.isLB_pull (O1_isLB R m) (pullback.fst (PSpace.str R m) (PSpace.str R n))
  have hM := LB.isLB_pull (O1_isLB R n) (pullback.snd (PSpace.str R m) (PSpace.str R n))
  exact ((isAmple_projective_O_one R m).box (isAmple_projective_O_one R n) (isLB_tw hL hM 1) (.of_hasPullback _ _)
    (exists_gen_div_div_tw hL hM)).isProjOver _

end Summary

end GlobalTheory

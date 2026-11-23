import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfDetMemNonZeroDivisors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardZerosOnTorsionLeOfSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

section Basic

theorem exists_polAV {Z : Scheme.{0}} (G : Over Z) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (g : ℕ)
    (hd : SmoothOfRelativeDimension g G.hom) (L : RigLB G) (hs : L.IsSymmetric) (W : Z.Opens)
    (ha : RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    (hk : KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    {K : Type} [Field K] (x : Sp K ⟶ Z) (hx : Set.range x ⊆ W) :
    ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ G.left), IsGrpPullback A.A G x φ ∧ LBIso A.L (L.L.pull φ) ∧ A.g = g := by
  obtain ⟨x', hx'⟩ : ∃ x' : Sp K ⟶ W.toScheme, x' ≫ W.ι = x :=
    ⟨IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G x
  have h₀ := isGrpPullback_pullback G W.ι
  have h₂ := h.congr hx'.symm rfl
  let ψ : ((Over.pullback x).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom W.ι = pullback.fst G.hom x := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback x).obj G) ((Over.pullback W.ι).obj G) x' ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB L.isLB (pullback.fst G.hom x)
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom W.ι)
  obtain ⟨w, hw⟩ : LBIso (L.L.pull (pullback.fst G.hom x)) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => pullback.fst G.hom x) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl hL)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := W.toScheme) (U := ⊤)
    (x := x' (IsLocalRing.closedPoint K)) trivial
  have hamp : RelAmple ((Over.pullback x).obj G) (L.L.pull (pullback.fst G.hom x)) :=
    relAmple_pull h₃.1 hL₀ hL ((isGen_iff w).1 hw) V hV
      (fun y => by rwa [Subsingleton.elim (α := PrimeSpectrum K) y (IsLocalRing.closedPoint K)]) ha
  have hsa := IsSemiAbelian.pullback x G hG
  have hA : IsAbelianScheme ((Over.pullback x).obj G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := projProper _ _ _ (ProjSpace.isProjOver_of_relAmple hamp)
      geomConnected := hsa.geomConnected }
  exact ⟨{ A := (Over.pullback x).obj G
           isAb := hA
           g := g
           smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hd
           L := L.L.pull (pullback.fst G.hom x)
           isLB := hL
           rigid := PolBaseChange.rigidified_pull h ⟨L.rig, L.rigGen⟩
           sym := PolBaseChange.sym_pull h (CechPic.sym_of_isSymmetric L hs)
           ample := hamp
           ktriv := kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk },
    pullback.fst G.hom x, h, PolBaseChange.lbIso_refl hL, rfl⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isOpen_TT_eq_bot (S : ThetaSys o Ω) (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  haveI : NeZero (S.r * S.N) := ⟨(Nat.mul_pos S.r_pos (lt_of_lt_of_le two_pos S.N_ge)).ne'⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {z' | M.Div S.th x z'}, fun z' hz' => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hle : S.HH M z ≤ S.HH M z' := AddSubgroup.closure_mono fun x hx => Set.mem_iInter₂.1 hz' x hx
  refine eq_bot_iff.2 fun a ha => ?_
  have : a ∈ S.TT M z := fun h hh => ha h (hle hh)
  rwa [show S.TT M z = ⊥ from hz] at this

theorem exists_unit (M : RatModel o Ω) {W : M.Z.Opens} (hW : (W : Set M.Z).Nonempty) {x : Ω} (h0 : x ≠ 0)
    (h : ∀ z ∈ W, x ∈ M.O z) (h' : ∀ z ∈ W, x⁻¹ ∈ M.O z) : ∃ u : Γ(M.Z, W)ˣ, M.res W hW u.val = x := by
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 h)
  obtain ⟨f', hf'⟩ := (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 h')
  rw [← M.res_apply W hW] at hf hf'
  have e : f * f' = 1 := M.res_injective W hW (by rw [map_mul, hf, hf', map_one, mul_inv_cancel₀ h0])
  exact ⟨⟨f, f', e, (mul_comm _ _).trans e⟩, hf⟩

theorem exists_GL (M : RatModel o Ω) {W : M.Z.Opens} (hW : (W : Set M.Z).Nonempty) {I : Type} [Fintype I] [DecidableEq I]
    {A A' : Matrix I I Ω} (h0 : A * A' = 1) (h : ∀ z ∈ W, ∀ i j, A i j ∈ M.O z) (h' : ∀ z ∈ W, ∀ i j, A' i j ∈ M.O z) :
    ∃ u : GL I Γ(M.Z, W), (M.res W hW).mapMatrix u.val = A := by
  choose f hf using fun i j => (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 fun z hz => h z hz i j)
  choose f' hf' using fun i j => (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 fun z hz => h' z hz i j)
  have e₁ : (M.res W hW).mapMatrix (Matrix.of f) = A := Matrix.ext fun i j => (M.res_apply W hW _).trans (hf i j)
  have e₂ : (M.res W hW).mapMatrix (Matrix.of f') = A' := Matrix.ext fun i j => (M.res_apply W hW _).trans (hf' i j)
  have e : Matrix.of f * Matrix.of f' = 1 := Matrix.map_injective (M.res_injective W hW)
    (show (M.res W hW).mapMatrix _ = (M.res W hW).mapMatrix _ by rw [map_mul, e₁, e₂, map_one, h0])
  exact ⟨⟨Matrix.of f, Matrix.of f', e, mul_eq_one_comm.1 e⟩, e₁⟩

theorem exists_ample (M : RatModel o Ω) {I : Type} (U : I → M.Z.Opens) (u : I → Ω) (hcov : ∀ z, ∃ i, z ∈ U i)
    (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty) (hu : ∀ i, u i ≠ 0)
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ g : ∀ i j, Γ(M.Z, U i ⊓ U j)ˣ, (LB.mk I U g).IsLB ∧
      (∀ z : M.Z, ∃ (d : ℕ) (s : H0 (LB.mk I U g) d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) ∧
      ∀ i j, M.res _ (M.nonempty_inf (hne i) (hne j)) (g i j).val = u j / u i := by
  have n₂ : ∀ i j, ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := fun i j => M.nonempty_inf (hne i) (hne j)
  choose g hg using fun i j => exists_unit M (n₂ i j) (div_ne_zero (hu j) (hu i)) (fun z hz => hreg i j z hz.1)
    (fun z hz => by rw [inv_div]; exact hreg j i z hz.2)
  choose f hf using fun q i => (RatModel.mem_ringOn_iff_exists (hne i)).1 (RatModel.mem_ringOn.2 (hreg i q))
  refine ⟨g, ⟨top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 (hcov z), fun i => ?_, fun i j k => ?_⟩,
    fun z => ?_, hg⟩
  · refine Units.ext (M.res_injective _ (hne i) ?_)
    refine (M.res_resG _ (hne i) _).trans ((hg i i).trans ?_)
    rw [div_self (hu i), Units.val_one, map_one]
  · have n₃ := M.nonempty_inf (n₂ i j) (hne k)
    refine Units.ext (M.res_injective _ n₃ ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ((M.res_resG _ n₃ _).trans (hg i j))
      ((M.res_resG _ n₃ _).trans (hg j k))).trans (Eq.trans ?_ ((M.res_resG _ n₃ _).trans (hg i k)).symm))
    have := hu i
    have := hu j
    field_simp
  · obtain ⟨q, hq⟩ := hcov z
    let s : (LB.mk I U g).Sec := ⟨f q, fun i j => M.res_injective _ (n₂ i j) (by
      refine ((M.res_resG _ (n₂ i j) _).trans ((M.res_apply _ _ _).trans (hf q i))).trans (Eq.trans ?_
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hg i j)
          ((M.res_resG _ (n₂ i j) _).trans ((M.res_apply _ _ _).trans (hf q j))))).symm)
      have := hu i
      have := hu j
      field_simp)⟩
    have e : nonzeroLocus s = U q := by
      have key : ∀ i, ∀ y ∈ U i, y ∈ M.Z.basicOpen (f q i) ↔ u i / u q ∈ M.O y := fun i y hy => by
        rw [← RatModel.isUnit_valF_iff hy, RatModel.isUnit_O_iff]
        simp only [hf, inv_div, ne_eq, div_ne_zero (hu q) (hu i), not_false_eq_true, true_and]
      refine le_antisymm (iSup_le fun i y hy => ?_) fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
      · have hy' := M.Z.basicOpen_le _ hy
        exact hconv i q y hy' ((key i y hy').1 hy)
      · exact (key q y hy).2 (hreg q q y hy)
    obtain ⟨s', e', -⟩ := exists_sec_oneTerm (LB.mk I U g) (K' := Fin 1) (e' := ((1 : ℕ) : ℤ)) rfl (TorsionZero.secOne s)
    rw [TorsionZero.nonzeroLocus_secOne, e] at e'
    exact ⟨1, s', le_rfl, by rw [e']; exact ⟨hq, haff q⟩⟩

theorem mem_span_rows_iff (A : Subalgebra o Ω) {J : Type} [Fintype J] [DecidableEq J] {b : Matrix J J Ω} (hb : b.det ≠ 0)
    (v : J → Ω) : v ∈ Submodule.span A (Set.range b) ↔ ∀ i, Matrix.vecMul v b⁻¹ i ∈ A := by
  have hb' : IsUnit b.det := hb.isUnit
  have key : ∀ c : J → A, ∑ i, c i • b i = Matrix.vecMul (fun i => (c i : Ω)) b := fun c => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) A).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hb', Matrix.vecMul_one]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v b⁻¹) b = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hb', Matrix.vecMul_one]

theorem eq_span_dual (A : Subalgebra o Ω) {J : Type} [Fintype J] [DecidableEq J] {b B : Matrix J J Ω} (hb : b.det ≠ 0)
    (hB : B.det ≠ 0) (h : ∀ w, w ∈ Submodule.span A (Set.range B) ↔ ∀ v ∈ Submodule.span A (Set.range b), w ⬝ᵥ v ∈ A) :
    Submodule.span A (Set.range b) = Submodule.span A (Set.range (B⁻¹).transpose) := by
  have hB' : (B⁻¹).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_nonsing_inv_det _ hB.isUnit).ne_zero
  have e : ((B⁻¹).transpose)⁻¹ = B.transpose := by
    rw [Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hB.isUnit)]
  ext v
  rw [mem_span_rows_iff A hB', e, Matrix.vecMul_transpose]
  refine ⟨fun hv i => (h (B i)).1 (Submodule.subset_span ⟨i, rfl⟩) v hv, fun hv => (mem_span_rows_iff A hb v).2 fun i => ?_⟩
  have h₁ : (b⁻¹).transpose i ∈ Submodule.span A (Set.range B) := (h _).2 fun v' hv' => by
    rw [dotProduct_comm]; exact (mem_span_rows_iff A hb v').1 hv' i
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 h₁
  show v ⬝ᵥ (b⁻¹).transpose i ∈ A
  rw [← hc, dotProduct_sum]
  refine sum_mem fun k _ => ?_
  rw [dotProduct_smul, dotProduct_comm]
  exact A.mul_mem (c k).2 (hv k)

end Basic

section Sections

variable {X Y : Scheme.{0}} (L : LB X) (k : ℤ)

abbrev powAlong (F : Y ⟶ X) : LB Y := LB.LinComb L (K := Fin 1) (fun _ => F) (fun _ => k)

variable {L k} {V : X.Opens}

theorem chart_le {F : Y ⟶ X} (hF : ∀ y, F y ∈ V) (j : Fin 1 → L.ι) :
    (powAlong L k F).U j ≤ F ⁻¹ᵁ (V ⊓ (powAlong L k (𝟙 X)).U j) := fun y hy =>
  ⟨hF y, Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a⟩

theorem gs_appLE {F : Y ⟶ X} (hF : ∀ y, F y ∈ V) (j : Fin 1 → L.ι) (a : Γ(X, V ⊓ (powAlong L k (𝟙 X)).U j))
    {T : Scheme.{0}} (r : T ⟶ Y) (z : T) (hz : r z ∈ (powAlong L k F).U j) :
    gs r z _ ((F.appLE _ _ (chart_le hF j)).hom a) = gs (r ≫ F) z _ a :=
  (gs_res r z (chart_le hF j) hz ((F.app _).hom a)).trans (gs_pull r F z _ (chart_le hF j hz) a)

def pullOn {σ : ∀ j, Γ(X, V ⊓ (powAlong L k (𝟙 X)).U j)} (hσ : σ ∈ secOn (powAlong L k (𝟙 X)) V) (F : Y ⟶ X)
    (hF : ∀ y, F y ∈ V) : (powAlong L k F).Sec where
  f j := (F.appLE _ _ (chart_le hF j)).hom (σ j)
  compat j j' := fn_ext fun y hy => by
    have m := chart_le hF j hy.1
    have m' := chart_le hF j' hy.2
    refine ((gs_res (𝟙 Y) y _ hy _).trans (gs_appLE hF j _ _ y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (gs_appLE hF j' _ _ y hy.2)))).symm)
    refine (ThetaUnit.gs_secOn hσ (𝟙 Y ≫ F) y m.1 m.2 m'.2).trans (congrArg (· * _) (congrArg Units.val ?_))
    refine (gm_linComb L _ _ (𝟙 Y ≫ F) y j j' m.2 m'.2).trans ?_
    simp only [Category.comp_id]

theorem valF_pullOn {σ : ∀ j, Γ(X, V ⊓ (powAlong L k (𝟙 X)).U j)} (hσ : σ ∈ secOn (powAlong L k (𝟙 X)) V) (F : Y ⟶ X)
    (hF : ∀ y, F y ∈ V) {K : Type} [Field K] (g : Sp K ⟶ Y) (j : Fin 1 → L.ι) :
    valF g _ ((pullOn hσ F hF).f j) = valF (g ≫ F) _ (σ j) := by
  by_cases h : ⊤ ≤ g ⁻¹ᵁ (powAlong L k F).U j
  · exact Points.valR_appLE g F _ h _
  · have h' : ¬ ⊤ ≤ (g ≫ F) ⁻¹ᵁ (V ⊓ (powAlong L k (𝟙 X)).U j) := fun h' =>
      h fun y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 (h' hy).2 a
    have e : valF (g ≫ F) _ (σ j) = 0 := dif_neg h'
    rw [e]
    exact dif_neg h

end Sections

section Family

variable {Z : Scheme.{0}} (G : Over Z) {L : LB G.left} (N : ℕ)

theorem snd_mem {T : Over Z} {W : Z.Opens} (hT : ∀ t, T.hom t ∈ W) (y : (T ⊗ G).left) :
    (snd T G).left y ∈ G.hom ⁻¹ᵁ W :=
  (congrArg (fun q => q y ∈ W) (LN.Frames.snd_hom G T)).mpr (hT _)

def secOver {W : Z.Opens} {σ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ (powAlong L N (𝟙 _)).U j)}
    (hσ : σ ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W)) (T : Over Z) (hT : ∀ t, T.hom t ∈ W) :
    LB.Sec (LPow G L (N : ℤ) T) :=
  pullOn hσ (snd T G).left (snd_mem G hT)

theorem lin_secOver {W W₁ W₂ : Z.Opens} {n : ℕ} {σ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W₁ ⊓ (powAlong L N (𝟙 _)).U j)}
    (hσ : σ ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W₁))
    {τ : Fin n → ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W₂ ⊓ (powAlong L N (𝟙 _)).U j)}
    (hτ : ∀ i, τ i ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W₂)) (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) (m : Fin n → Γ(Z, W))
    (H : ∀ (Y : Scheme.{0}) (r : Y ⟶ G.left) (y : Y) (j), G.hom (r y) ∈ W → r y ∈ (powAlong L N (𝟙 _)).U j →
      gs r y _ (σ j) = ∑ i, gs (r ≫ G.hom) y W (m i) * gs r y _ (τ i j))
    (h : Over.mk W.ι ⟶ Over.mk W₂.ι) (c : Fin n → Γ(W.toScheme, ⊤)) (hc : ∀ i, c i = W.topIso.inv.hom (m i)) :
    LN.Lin G L N h (fun i => secOver G N (hτ i) (Over.mk W₂.ι) (fun t => t.2)) c
      (secOver G N hσ (Over.mk W.ι) (fun t => h₁ t.2)) := by
  obtain rfl : c = fun i => W.topIso.inv.hom (m i) := funext hc
  intro z J hJ
  have hm : ∀ t : W.toScheme, W.ι t ∈ W := fun t => t.2
  have e : W.topIso.inv = W.ι.appLE W ⊤ (fun t _ => hm t) := (Scheme.Opens.ι_appLE W W ⊤ (fun t _ => hm t)).symm
  have mz := hJ.mem (fun _ : Fin 1 => (snd (Over.mk W.ι) G).left) (𝟙 _)
  refine (gs_appLE (snd_mem G (T := Over.mk W.ι) fun t => h₁ t.2) _ _ _ z mz).trans ((H _ _ z _ (snd_mem G (T := Over.mk W.ι) hm z)
    (Set.mem_iInter.2 fun a => Set.mem_iInter.1 mz a)).trans (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_))
  · show gs ((snd (Over.mk W.ι) G).left ≫ G.hom) z W (m i) = gs _ z ⊤ (W.topIso.inv.hom (m i))
    rw [LN.Frames.snd_hom, ← gs_pull _ (Over.mk W.ι).hom z _ (hm _), e]
    exact (gs_res (fst (Over.mk W.ι) G).left z (show ⊤ ≤ W.ι ⁻¹ᵁ W from fun t _ => hm t) trivial _).symm
  · refine Eq.trans ?_ (gs_appLE (snd_mem G (T := Over.mk W₂.ι) fun t => t.2) _ _ _ z
      (hJ.mem (fun _ : Fin 1 => (snd (Over.mk W₂.ι) G).left) (h ▷ G).left)).symm
    exact congrArg (fun F => gs F z _ (τ i fun _ => J F)) (LN.Frames.whisker_snd G h).symm

theorem indep_secOver {W : Z.Opens} {n : ℕ} {τ : Fin n → ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ (powAlong L N (𝟙 _)).U j)}
    (hτ : ∀ i, τ i ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W)) {K : Type} [Field K] (x : Sp K ⟶ W.toScheme) (c : Fin n → K)
    (H : ∀ (g : Sp K ⟶ (Over.mk W.ι ⊗ G).left) j, g ≫ (fst (Over.mk W.ι) G).left = x →
      ∑ i, c i * valF g _ ((secOver G N (hτ i) (Over.mk W.ι) (fun t => t.2)).f j) = 0)
    (g : Sp K ⟶ G.left) (j) (hg : g ≫ G.hom = x ≫ W.ι) : ∑ i, c i * valF g _ (τ i j) = 0 := by
  let g' : Sp K ⟶ (Over.mk W.ι ⊗ G).left := pullback.lift x g hg.symm
  have e : g' ≫ (snd (Over.mk W.ι) G).left = g := pullback.lift_snd _ _ _
  refine Eq.trans (Finset.sum_congr rfl fun i _ => congrArg (c i * ·) ?_) (H g' j (pullback.lift_fst _ _ _))
  exact ((valF_pullOn (hτ i) _ _ g' j).trans (by rw [e])).symm

end Family

section Generic

theorem eq_of_valF_generic {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (ξ : Sp K ⟶ X)
    (hξ : ∀ w, ξ w = genericPoint X) {U : X.Opens} (hU : ⊤ ≤ ξ ⁻¹ᵁ U) {a b : Γ(X, U)} (h : valF ξ U a = valF ξ U b) :
    a = b := by
  rw [← sub_eq_zero]
  by_contra h0
  have hne : ((X.basicOpen (a - b) : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => h0 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective e))
  have hu := (Points.le_preimage_basicOpen_iff ξ hU (a - b)).1 (top_le_preimage_of_specializes
    (fun w => by rw [hξ]; exact genericPoint_specializes _) hne.some_mem)
  refine hu.ne_zero ?_
  rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_eq ξ U hU, Points.valR_eq ξ U hU] at h
  rw [Points.valR_eq ξ U hU, map_sub, h, sub_self]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_eq_spMap_pt (M : RatModel o Ω) {K : Type} [Field K] (x : Sp K ⟶ M.Z)
    (hx : ∀ w, x w = genericPoint M.Z) : ∃ β : Ω →+* K, x = spMap β ≫ M.pt := by
  have hs : ∀ w, x w ⤳ genericPoint M.Z := fun w => hx w ▸ specializes_rfl
  have hm : ∀ a : Ω, a ∈ M.O (genericPoint M.Z) := fun a => by rw [M.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf x _ hs).comp ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)) hm)
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint M.Z) trivial
  have h₁ := top_le_preimage_of_specializes hs hz
  have h₂ := M.top_le_preimage_pt ⟨_, hz⟩
  refine ⟨β, Points.ext_of_valR hV h₁ (Points.le_preimage_comp _ _ h₂ (Points.le_preimage_top _)) fun f => ?_⟩
  rw [Points.valR_spMap_comp β M.pt V h₂]
  exact (RatModel.val_valF ((top_le_preimage_iff _ _).1 h₁) f).symm

variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE)

theorem rel_of_genVal (hU₀ : (U₀ : Set M.Z).Nonempty) (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) {W W₁ W₂ : M.Z.Opens} (h₁ : W ≤ W₁) (h₂ : W ≤ W₂)
    {n : ℕ} {c : I → Ω} {d : Fin n → I → Ω} {σ} {τ : Fin n → _}
    (hσ : GenVal ρ M U₀ Z.u₀ Z.G Z.φ Z.L.L Z.w k t c (Z.G.hom ⁻¹ᵁ W₁) σ)
    (hτ : ∀ i, GenVal ρ M U₀ Z.u₀ Z.G Z.φ Z.L.L Z.w k t (d i) (Z.G.hom ⁻¹ᵁ W₂) (τ i))
    (m : Fin n → Γ(M.Z, W)) (hm : ∀ l, c l = ∑ i, valF M.pt W (m i) * d i l)
    (Y : Scheme.{0}) (r : Y ⟶ Z.G.left) (y : Y) (j) (hy : Z.G.hom (r y) ∈ W)
    (hj : r y ∈ (powAlong Z.L.L k (𝟙 _)).U j) :
    gs r y _ (σ j) = ∑ i, gs (r ≫ Z.G.hom) y W (m i) * gs r y _ (τ i j) := by
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  have := Z.semi
  have : IsIntegral Z.G.left := isIntegral_left_of_isSemiAbelian Z.G
  let K : Type := Z.G.left.residueField (genericPoint Z.G.left)
  let ξ : Sp K ⟶ Z.G.left := Z.G.left.fromSpecResidueField _
  have hξ : ∀ w, ξ w = genericPoint Z.G.left := fun w => Scheme.fromSpecResidueField_apply _ w
  have hξU : ∀ {U : Z.G.left.Opens} {x}, x ∈ U → ⊤ ≤ ξ ⁻¹ᵁ U := fun {U x} hx =>
    top_le_preimage_of_specializes (fun w => by rw [hξ]; exact genericPoint_specializes _) hx
  have hsurj : Function.Surjective Z.G.hom := fun z => ⟨eSec Z.G z, congrArg (fun q => q z) (Over.w η[Z.G])⟩
  have hgen : ∀ w, (ξ ≫ Z.G.hom) w = genericPoint M.Z := fun w => by
    have := (genericPoint_spec Z.G.left).image Z.G.hom.continuous
    rw [Set.image_univ, hsurj.range_eq, closure_univ, ← hξ w] at this
    exact this.eq (genericPoint_spec M.Z)
  obtain ⟨β, hβ⟩ := exists_eq_spMap_pt M _ hgen
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Sp K ⟶ U₀.toScheme, x₀ ≫ U₀.ι = ξ ≫ Z.G.hom :=
    ⟨IsOpenImmersion.lift U₀.ι _ (by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, hgen]
      exact (genericPoint_specializes _).mem_open U₀.isOpen hU₀.some_mem), IsOpenImmersion.lift_fac _ _ _⟩
  let g : Sp K ⟶ pullback ρ.P.A.hom Z.u₀ := Z.cart.1.lift ξ x₀ hx₀.symm
  have hg₁ : g ≫ Z.φ = ξ := Z.cart.1.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd _ _ = x₀ := Z.cart.1.lift_snd _ _ _
  let p : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (g ≫ pullback.fst _ _ ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _) (by simp)
  have hp : p ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := pullback.lift_snd _ _ _
  obtain ⟨jP, hjP⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Z.u₀) (IsLocalRing.closedPoint K))
  have a₁ : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt := by rw [← Category.assoc, hg₂, hx₀, hβ]
  have a₂ : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Z.u₀) ⁻¹ᵁ ρ.P.L.U jP := (Points.le_preimage_iff _ _).2 hjP
  have a₃ : ⊤ ≤ (g ≫ Z.φ) ⁻¹ᵁ Z.L.L.U jL := by rw [hg₁]; exact hξU (Set.mem_iInter.1 hj 0)
  have e₁ := hσ K β g p jP jL a₁ hp ((top_le_preimage_iff _ _).1 a₂) ((top_le_preimage_iff _ _).1 a₃)
    ((top_le_preimage_iff _ _).1 (by rw [hg₁]; exact hξU (x := r y) (h₁ hy)))
  have e₂ := fun i => hτ i K β g p jP jL a₁ hp ((top_le_preimage_iff _ _).1 a₂) ((top_le_preimage_iff _ _).1 a₃)
    ((top_le_preimage_iff _ _).1 (by rw [hg₁]; exact hξU (x := r y) (h₂ hy)))
  rw [hg₁] at e₁ e₂
  have hw : valF g _ (Z.w.s (fun _ => jP, fun _ => jL)).val ≠ 0 := by
    have hle : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Z.u₀)) (Z.L.L.pull Z.φ)).U (fun _ => jP, fun _ => jL) :=
      fun w hw => ⟨mem_pull.2 (a₂ hw), mem_pull.2 (a₃ hw)⟩
    rw [Points.valF_eq_valR, Points.valR_eq g _ hle]
    exact ((Units.isUnit _).map _).ne_zero
  have e₃ : valF ξ _ (σ fun _ => jL) = ∑ i, β (valF M.pt W (m i)) * valF ξ _ (τ i fun _ => jL) := by
    refine mul_left_cancel₀ (zpow_ne_zero k hw) ?_
    rw [← e₁, Finset.mul_sum]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (congrArg (β (valF M.pt W (m i)) * ·) (e₂ i)).trans
      (mul_left_comm _ _ _))
    simp only [hm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
    rw [Finset.sum_comm]
  let O : Z.G.left.Opens := Z.G.hom ⁻¹ᵁ W ⊓ (powAlong Z.L.L k (𝟙 _)).U fun _ => jL
  have hO : r y ∈ O := ⟨hy, hj⟩
  have l₁ : O ≤ Z.G.hom ⁻¹ᵁ W₁ ⊓ (powAlong Z.L.L k (𝟙 _)).U fun _ => jL := fun x hx => ⟨h₁ hx.1, hx.2⟩
  have l₂ : O ≤ Z.G.hom ⁻¹ᵁ W₂ ⊓ (powAlong Z.L.L k (𝟙 _)).U fun _ => jL := fun x hx => ⟨h₂ hx.1, hx.2⟩
  have e₄ : resG _ l₁ (σ fun _ => jL) =
      ∑ i, resG _ (inf_le_left : O ≤ _) ((Z.G.hom.app W).hom (m i)) * resG _ l₂ (τ i fun _ => jL) := by
    refine eq_of_valF_generic ξ hξ (hξU hO) (((Points.valR_res ξ l₁ (hξU hO) _).trans e₃).trans (Eq.symm ?_))
    rw [Points.valF_eq_valR, Points.valR_eq ξ O (hξU hO), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← Points.valR_eq, ← Points.valR_eq]
    refine congrArg₂ (· * ·) ((Points.valR_res ξ _ (hξU hO) _).trans ((Points.valR_comp ξ Z.G.hom W _).symm.trans ?_))
      (Points.valR_res ξ l₂ (hξU hO) _)
    rw [hβ]
    exact Points.valR_spMap_comp β M.pt W (M.top_le_preimage_pt ⟨_, hy⟩) _
  refine (gs_res r y l₁ hO _).symm.trans ((congrArg (gs r y O) e₄).trans ?_)
  rw [gs_eq r y O hO, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r y O hO, gs_mul r y O hO]
  exact congrArg₂ (· * ·) ((gs_res r y _ hO _).trans (gs_pull r Z.G.hom y W hy _)) (gs_res r y l₂ hO _)

end Generic

end GlobalTheory.AmpModel

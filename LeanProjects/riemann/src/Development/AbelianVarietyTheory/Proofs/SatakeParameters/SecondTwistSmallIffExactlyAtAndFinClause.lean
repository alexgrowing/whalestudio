import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BlockSumMultiplicities
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace GlobalTheory.Cmp.SmallJumps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW Module
open GlobalTheory.IndefiniteRowSideFullHecke

theorem finite_of_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) (anti : ∀ a, F (a + 1) ≤ F a) (exh : ∀ x ∈ U, ∃ a, x ∈ F a)
    (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) :
    FiniteDimensional L U := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  have hd : Antitone fun a => finrank L (F a) := antitone_int_of_succ_le fun a => by
    have := h a
    omega
  obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero hJ
  have hpos : 0 < finrank L (F a₀) := by
    have := h a₀
    have := Multiset.count_pos.2 ha₀
    omega
  have hfin : ∀ a ≤ a₀, FiniteDimensional L (F a) := fun a ha =>
    Module.finite_of_finrank_pos (lt_of_lt_of_le hpos (hd ha))
  obtain ⟨b, hb⟩ := J.toFinset.bddBelow
  have hb' : ∀ a ∈ J, b ≤ a := fun a ha => hb (by simpa using ha)
  have hb0 : b ≤ a₀ := hb' a₀ ha₀
  have hst : ∀ a ≤ b, F a = F b := by
    intro a ha
    induction a, ha using Int.le_induction_down with
    | base => rfl
    | pred a ha ih =>
      haveI := hfin (a - 1) (by omega)
      have h1 := h (a - 1)
      have h2 : J.count (a - 1) = 0 := Multiset.count_eq_zero.2 fun hm => by
        have := hb' _ hm
        omega
      rw [sub_add_cancel, h2] at h1
      rw [← ih]
      exact (Submodule.eq_of_le_of_finrank_eq (hA (by omega)) (by omega)).symm
  haveI := hfin b hb0
  refine Submodule.finiteDimensional_of_le (S₂ := F b) fun x hx => ?_
  obtain ⟨a, ha⟩ := exh x hx
  rcases le_total a b with hab | hab
  · rwa [← hst a hab]
  · exact hA hab ha

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_anti : Antitone fun a => FilV PD (LL := LL) (V := V) a := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem filV_exh (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem finite_ddRE_of_multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, multV PD ρ τ a = (J.count a : ℤ)) : FiniteDimensional LL (DdRE PD ρ τ) :=
  finite_of_jumps (FildR PD ρ τ) _
    (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
    (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) J hJ h

end Periods

theorem linearIndepOn_of_invariant {K F W G ι : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn F v s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx' : x ∉ (s : Set ι) := hx
    rw [Finset.coe_insert, linearIndepOn_insert hx'] at h ⊢
    refine ⟨ih h.1, fun hm => h.2 ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F).1 hm
    have key : ∀ i ∈ s, ∀ g, a g (c i) = c i := by
      intro i hi g
      have h1 : ∑ i ∈ s, a g (c i) • v i = v x := by
        rw [← hv g x, ← hc, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hσ, hv]
      have h2 := linearIndepOn_finset_iff.1 (ih h.1) (fun j => a g (c j) - c j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, h1, hc, sub_self]) i hi
      exact sub_eq_zero.1 h2
    rw [← hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨k, hk⟩ := hinv _ (key i hi)
    rw [← hk, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem finite_of_invariant {K F W G : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] [Module.Finite F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (U : Submodule K W)
    (hU : ∀ x ∈ U, ∀ g, σ g x = x) : Module.Finite K U := by
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := finrank F W) fun s hs => ?_) (Cardinal.natCast_lt_aleph0)
  have h1 : LinearIndepOn K (fun x : U => (x : W)) s := hs.map' U.subtype U.ker_subtype
  have h2 := linearIndepOn_of_invariant a σ hσ hinv (fun x : U => (x : W))
    (fun g x => hU x x.2 g) s h1
  simpa using LinearIndependent.fintype_card_le_finrank h2

section FieldPeriods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finite_ddR_of_isField (hF : IsField BdR) [Module.Finite Qp V] (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) := by
  letI : Field BdR := hF.toField
  haveI := PD.finK
  let σ : G → TensorProduct Qp BdR V →ₗ[Qp] TensorProduct Qp BdR V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  let U : Submodule K (TensorProduct Qp BdR V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add, hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }
  haveI : Module.Finite K U := finite_of_invariant (F := BdR) (fun g b => PD.actdR g b)
    (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  let f : DdR PD ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by
        have := x.2
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }
  haveI : Module.Finite Qp (DdR PD ρ) := Module.Finite.of_injective f fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))
  exact Module.Finite.of_restrictScalars_finite Qp LL _

end FieldPeriods

variable (D : D7)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem over_iff (τ : BlockSumMultiplicities.Emb D i w hw) (g : D.R.GG) :
    BlockSumMultiplicities.Over D i w hw τ g ↔ CrystallineAtPlaces.Reads D i w hw τ g := by
  refine forall_congr' fun x => ⟨?_, fun h => ⟨_, h.symm, CrystallineAtPlaces.embLL_sigmaOf g x⟩⟩
  rintro ⟨y, h1, h2⟩
  have : y = D.embE (D.host.sigmaOf g x) :=
    D.what₂.embLL.injective (h2.trans (CrystallineAtPlaces.embLL_sigmaOf g x).symm)
  rw [← this, h1]

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))

theorem mult_eq (τ : BlockSumMultiplicities.Emb D i w hw) (a : ℤ) :
    BlockSumMultiplicities.mult D i w hw M τ a = CrystallineAtPlaces.mult D i w hw M τ a := rfl

end Place

def FinClause : Prop :=
  ∀ (i : D.nd.Loc) (r : BlockSumMultiplicities.Fam D i D.R.nV) (ρ : BlockSumMultiplicities.Fam D i D.R.r) (π : D.nd.X i),
    BlockSumMultiplicities.HidaSetting D i r ρ π → ∀ w hw (τ : BlockSumMultiplicities.Emb D i w hw),
      BlockSumMultiplicities.FinDR D i w hw (T2O D.nd i ρ π) τ

variable {D}

def JumpsByLetterAt (L : SizeData₂ D) (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : BlockSumMultiplicities.Fam D i D.R.nV) (ρ : BlockSumMultiplicities.Fam D i D.R.r) (π : D.nd.X i),
    CrystallineAtPlaces.HidaSetting D i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrystallineAtPlaces.CrysInput D i w hw r → CrystallineAtPlaces.JumpInput D i w hw ε r →
      CrystallineAtPlaces.CrysAt D i w hw (T2O D.nd i ρ π) ∧
      ∀ τ g, CrystallineAtPlaces.Reads D i w hw τ g →
        CrystallineAtPlaces.HasJumps D i w hw (T2O D.nd i ρ π) τ
          (jT2 (hcAt D g) (CrystallineAtPlaces.liftIdx D i) (pos ε g)) ∧
        ((etaHat L : ℤ) < szT (hcAt D g) (CrystallineAtPlaces.liftIdx D i) (pos ε g) →
          CrystallineAtPlaces.countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m)

end GlobalTheory.Cmp.SmallJumps

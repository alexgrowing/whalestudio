import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsTer
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV.AwayLat

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem localization_mono {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    {L N : Submodule (𝓞 E) W} (h : L ≤ N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem le_localized_self {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    (L : Submodule (𝓞 E) W) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L := fun x hx =>
  ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

theorem localization_le_of_le_localization₂ {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    {L N : Submodule (𝓞 E) W} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx'⟩

theorem sup_smul_le_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    (I : Ideal (𝓞 E)) {A A' B B' : Submodule (𝓞 E) W} (hA : A ≤ Formalism.HermitianLatticesTheory.localization₂ p A') (hB : B ≤ Formalism.HermitianLatticesTheory.localization₂ p B') :
    A ⊔ I • B ≤ Formalism.HermitianLatticesTheory.localization₂ p (A' ⊔ I • B') := by
  refine sup_le (hA.trans (localization_mono p le_sup_left)) ?_
  refine Submodule.smul_le.2 fun r hr m hm => ?_
  obtain ⟨s, hs, hsm⟩ := hB hm
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)

theorem map_le_locP {n : ℕ} (p : Ideal (𝓞 E)) [p.IsPrime] (f : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M') :
    M.map ((f : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤
      Formalism.HermitianLatticesTheory.localization₂ p (M'.map ((f : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨s, hs, hsm⟩ := h hm
  exact ⟨s, hs, ⟨s • m, hsm, by simp⟩⟩

theorem hform_smul_right {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E) (x y : Fin n → E) :
    hform σ J x (c • y) = algebraMap (𝓞 E) E c * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E) (x y : Fin n → E) :
    hform σ J (c • x) y = σ (algebraMap (𝓞 E) E c) * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_add_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_zero_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hform σ J 0 y = 0 := by
  simp [hform]

theorem dualSet_le_locP {n : ℕ} (σ : E →+* E) (e : 𝓞 E ≃+* 𝓞 E)
    (he : ∀ t : 𝓞 E, σ (algebraMap (𝓞 E) E t) = algebraMap (𝓞 E) E (e t))
    (J : Matrix (Fin n) (Fin n) E) {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (hf : Module.Finite (𝓞 E) Λ')
    (I I' : Ideal (𝓞 E)) [I.IsPrime] [I'.IsPrime] (hI : ∀ t, t ∉ I' → e t ∉ I) (h : Λ' ≤ Formalism.HermitianLatticesTheory.localization₂ I' Λ) :
    Formalism.BasicNotions.dualSet σ J Λ ⊆ Formalism.HermitianLatticesTheory.localization₂ I (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ J Λ')) := by
  classical
  intro y hy
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hf
  have ht : ∀ g ∈ G, ∃ t : 𝓞 E, t ∉ I' ∧ t • g ∈ Λ := fun g hg => by
    obtain ⟨t, ht, htg⟩ := h (hG ▸ Submodule.subset_span hg)
    exact ⟨t, ht, htg⟩
  choose! t ht1 ht2 using ht
  refine ⟨∏ g ∈ G, e (t g), fun hmem => ?_, Submodule.subset_span ?_⟩
  · obtain ⟨g, hg, hgI⟩ := (Ideal.IsPrime.prod_mem_iff (p := I)).1 hmem
    exact hI _ (ht1 g hg) hgI
  · intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem g hg =>
      rw [hform_smul_right, ← Finset.mul_prod_erase G _ hg, map_mul, mul_assoc, ← he, mul_left_comm, ← hform_smul_left]
      obtain ⟨r, hr⟩ := hy _ (ht2 g hg)
      rw [← hr, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨r', hr'⟩ := hx'
      rw [hform_add_left, ← hr, ← hr', ← map_add]
      exact ⟨_, rfl⟩
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := hx
      rw [hform_smul_left, he, ← hr, ← map_mul]
      exact ⟨_, rfl⟩

end Gen

section SeamT

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (iE : K ≃+* K') {m : ℕ}

theorem algebraMap_mapRingEquiv (t : 𝓞 K) :
    algebraMap (𝓞 K') K' (RingOfIntegers.mapRingEquiv iE t) = iE (algebraMap (𝓞 K) K t) := rfl

theorem exists_of_mem_span_image (N : Submodule (𝓞 K) (Fin m → K)) (z : Fin m → K')
    (hz : z ∈ Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N : Set (Fin m → K)))) :
    ∃ w ∈ N, (fun i => iE (w i)) = z := by
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨w, hw, rfl⟩ := hz; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, N.zero_mem, funext fun i => by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨w', hw', rfl⟩ := hz'
    exact ⟨w + w', N.add_mem hw hw', funext fun i => by simp⟩
  | smul c z _ hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨(RingOfIntegers.mapRingEquiv iE).symm c • w, N.smul_mem _ hw, funext fun i => ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rw [← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]

theorem mem_equivOfRingEquiv (P : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) :
    RingOfIntegers.mapRingEquiv iE t ∈ (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv iE) P).asIdeal ↔
      t ∈ P.asIdeal := by
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

theorem le_localized_of_transport (N N₁ : Submodule (𝓞 K) (Fin m → K)) (P : HeightOneSpectrum (𝓞 K))
    (h : Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N₁ : Set (Fin m → K))) ≤
      Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv iE) P).asIdeal
        (Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N : Set (Fin m → K))))) :
    N₁ ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  intro y hy
  obtain ⟨c, hc, hcy⟩ := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨w, hw, hwz⟩ := exists_of_mem_span_image iE N _ hcy
  refine ⟨(RingOfIntegers.mapRingEquiv iE).symm c, fun hP => hc ?_, ?_⟩
  · have := (mem_equivOfRingEquiv iE P _).2 hP
    rwa [RingEquiv.apply_symm_apply] at this
  · convert hw using 1
    funext i
    apply iE.injective
    have := congrFun hwz i
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul] at this ⊢
    rw [this, ← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]

end SeamT

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) : ∃ ν : 𝓞 E, ν ≠ 0 ∧ ν • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.FiniteIndexSubgroup.target
  | exact _root_.GlobalTheory.FiniteIndexSubgroup.target
  | (apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteIndexSubgroup.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteIndexSubgroup.target ..)

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem incl_smul (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 E) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((s • x) i)) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E s) •
        fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]

theorem mem_localization_of_mem_localLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (B : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) B → Submodule.span E (B : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v B → ∀ q : HeightOneSpectrum (𝓞 E), q.under (𝓞 F) = v → x ∈ Formalism.HermitianLatticesTheory.localization₂ q.asIdeal B := by
  intro F E _ _ _ _ _ n v B hB hs x hx q hq
  classical
  obtain ⟨ν, hν, hνx⟩ := exists_smul_mem_of_span B hs x
  let J : Ideal (𝓞 E) := B.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hJ : ∀ s, s ∈ J ↔ s • x ∈ B := fun s => Iff.rfl
  have hJ0 : J.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    intro h
    have := Ideal.eq_bot_of_comap_eq_bot h
    have h2 : ν ∈ J := hνx
    rw [this] at h2
    exact hν h2
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 v.asIdeal
  obtain ⟨d, hdQ, hdv⟩ : ∃ d ∈ Q, d ∉ v.asIdeal := by
    by_contra h
    push_neg at h
    rw [sup_eq_left.2 (show Q ≤ v.asIdeal from h)] at hQ
    exact v.isPrime.ne_top hQ
  refine ⟨algebraMap (𝓞 F) (𝓞 E) d, fun h => hdv (by rw [← hq]; exact h), ?_⟩
  refine (GlobalTheory.LatLocGlob.latS_local_global F E n B hB).2.1 hs _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [incl_smul]
    exact Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B)
      (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, ⟨algebraMap (𝓞 F) (𝓞 E) d, rfl⟩⟩, rfl⟩)⟩ : intV E w) hx
  · obtain ⟨π, hπ, hπw⟩ : ∃ π ∈ v.asIdeal ^ (UniqueFactorizationMonoid.normalizedFactors (J.comap (algebraMap (𝓞 F) (𝓞 E)))).count v.asIdeal, π ∉ w.asIdeal := by
      by_contra h
      push_neg at h
      haveI := w.isPrime
      have h1 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h1).symm)
    have h1 : π * d ∈ J.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [hI]; exact Ideal.mul_mem_mul hπ hdQ
    have h2 : algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x ∈ B := by
      rw [← mul_smul, ← map_mul]; exact h1
    obtain ⟨t, ht, e⟩ := GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) w π hπw
    have h3 : (fun i => Formalism.UG.inclE (F := F) (w.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x) i)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B := Submodule.subset_span ⟨_, h2, rfl⟩
    have h4 := Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B) (⟨t, ht⟩ : intV E w) h3
    rw [incl_smul] at h4
    have e2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) = algebraMap F E (π : F) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [e2, Subring.smul_def, smul_smul] at h4
    rwa [show ((⟨t, ht⟩ : intV E w) : E ⊗[F] w.adicCompletion F) * _ = 1 from e, one_smul] at h4

end Loc

section Adel
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_locLat_iff_adelic (w : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (z : Fin n → E ⊗[F] w.adicCompletion F) :
    z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w L ↔ (fun i => Formalism.UG.P.afsplitIE w (z i)) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) L := by
  rw [GlobalTheory.LatticeStabLocal.mem_latS_adele_iff]
  have h1 : (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE w (z i))) = z :=
    funext fun i => Formalism.UG.P.afsplit_prV_IE w _
  constructor
  · intro hz v
    by_cases hv : v = w
    · subst hv; rw [h1]; exact hz
    · rw [show (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE w (z i))) = 0 from
        funext fun i => Formalism.UG.P.afsplit_prV_IE_ne w v hv _]
      exact zero_mem _
  · intro h
    have := h w
    rwa [h1] at this

end Adel

section LocB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_latS_globLat_iff (Lb : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Lb)
    (hs : Submodule.span E (Lb : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F))
        (Formalism.UG.CS.globLat g Lb) ↔
      ((g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _) *ᵥ X ∈
        Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb :=
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) Lb hf hs g X

theorem globLat_le_localization_globLat (Lb : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Lb)
    (hs : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (x x₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hQ : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)))
    (hx : Formalism.UG.bc (Formalism.UG.prV (E := E) v) x₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) x) :
    Formalism.UG.CS.globLat x Lb ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Formalism.UG.CS.globLat x₁ Lb) := by
  have hlat := fun g => Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) Lb hf hs g
  have hfin : ∀ g, Module.Finite (𝓞 E) (Formalism.UG.CS.globLat g Lb) := fun g => Module.Finite.iff_fg.2 (hlat g).fg
  have hq : Q.under (𝓞 F) = v := HeightOneSpectrum.ext hQ.symm
  intro z hz
  refine mem_localization_of_mem_localLattice F E n v _ (hfin x₁) (hlat x₁).span_eq_top z ?_ Q hq
  have hz' : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Formalism.UG.CS.globLat x Lb) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  rw [mem_locLat_iff_adelic v _ (hfin x₁), mem_latS_globLat_iff Lb hf hs]
  rw [mem_locLat_iff_adelic v _ (hfin x), mem_latS_globLat_iff Lb hf hs] at hz'
  set X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => Formalism.UG.P.afsplitIE v (Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i))
  have hp : ∀ p : HeightOneSpectrum (𝓞 F),
      (fun i => Formalism.UG.prV (E := E) p ((((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) =
        (fun i => Formalism.UG.prV (E := E) p ((((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) := by
    intro p
    rw [GlobalTheory.LatticeStabLocal.prV_mulVec, GlobalTheory.LatticeStabLocal.prV_mulVec]
    by_cases hpv : p = v
    · subst hpv
      have h1 : ((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E := E) p) =
          ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
      have h2 : ((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E := E) p) =
          ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
      rw [h1, h2, map_inv, map_inv, hx]
    · rw [show (fun i => Formalism.UG.prV (E := E) p (X i)) = 0 from funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v p hpv _,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
  have e : (((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) = (((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) := by
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun p => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun (hp p) i
  rw [e]
  exact hz'

end LocB

section Glue

theorem latAd_eq' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {N : ℕ}

theorem latCo_le_locP (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hf : Module.Finite (𝓞 E) Lb) (hs : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (y y₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Q Qc : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hQ : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (hQc : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)))
    (e : 𝓞 E ≃+* 𝓞 E) (he : ∀ t : 𝓞 E, (sp.cm.sig : E →+* E) (algebraMap (𝓞 E) E t) = algebraMap (𝓞 E) E (e t))
    (hI : ∀ t, t ∉ Qc.asIdeal → e t ∉ Q.asIdeal)
    (hy : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y) :
    latCo sp J co a y₁ Lb ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (latCo sp J co a y Lb) := by
  have hfin : Module.Finite (𝓞 E) (Formalism.UG.CS.globLat y Lb) :=
    Module.Finite.iff_fg.2 (Formalism.UG.P.global_lattice_isLattice_holds F E (Fin N) Lb hf hs y).fg
  unfold latCo mvL
  refine map_le_locP Q.asIdeal (toLE co) ?_
  unfold compan
  rw [latAd_eq', latAd_eq']
  refine sup_smul_le_locP Q.asIdeal _ (globLat_le_localization_globLat Lb hf hs y₁ y Q v hQ hy.symm) ?_
  exact Submodule.span_le.2 (dualSet_le_locP _ e he J hfin Q.asIdeal Qc.asIdeal hI (globLat_le_localization_globLat Lb hf hs y y₁ Qc v hQc hy))

end Glue

set_option maxHeartbeats 1000000 in

theorem lat_eq : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P
  classical
  set Q : HeightOneSpectrum (𝓞 D.host.E) := seamP t.seam P.1 with hQdef
  have hQS : Q ∈ ssRec t u μ := by
    rw [hQdef, mem_ssRec, ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]
    exact Finset.mem_union_left _ P.2
  set v : HeightOneSpectrum (𝓞 D.host.F) := Q.under (𝓞 D.host.F) with hvdef
  have hQv : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
  have hv : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x₁.1 = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x.1 :=
    hx v ⟨Q, hQS, hQv⟩
  set e : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) with hedef
  have hee : ∀ t' : 𝓞 D.host.E, e (e t') = t' := fun t' => Subtype.ext (star_star (t' : D.host.E))
  set Qc : HeightOneSpectrum (𝓞 D.host.E) := HeightOneSpectrum.equivOfRingEquiv e Q with hQcdef
  have hmemc : ∀ t' : 𝓞 D.host.E, e t' ∈ Qc.asIdeal ↔ t' ∈ Q.asIdeal := fun t' => mem_equivOfRingEquiv _ Q t'
  have hI : ∀ t', t' ∉ Qc.asIdeal → e t' ∉ Q.asIdeal := fun t' ht hQ => ht (by rw [← hee t']; exact (hmemc _).2 hQ)
  have hfixF : ∀ r : 𝓞 D.host.F, e (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
    intro r
    apply Subtype.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = _
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (r : D.host.F) := by
      show algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]
    rw [h1]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have hQcv : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [hQv]
    ext r
    simp only [Ideal.mem_comap]
    rw [← hmemc, hfixF]
  have he : ∀ t' : 𝓞 D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) (algebraMap (𝓞 D.host.E) D.host.E t') =
      algebraMap (𝓞 D.host.E) D.host.E (e t') := fun t' => rfl
  have hf := ((St j hj).K β).lev.Lb_fin
  have hs := ((St j hj).K β).lev.Lb_span
  have h1 := latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x.1 x₁.1 Q Qc v hQv hQcv e he hI hv
  have h2 := latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x₁.1 x.1 Q Qc v hQv hQcv e he hI hv.symm
  rw [← hp.lat, ← hp₁.lat] at h1
  rw [← hp.lat, ← hp₁.lat] at h2
  exact le_antisymm (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h1))
    (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h2))

end GlobalTheory.TwV.AwayLat

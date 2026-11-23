import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqInteger
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.SameOff

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) : ∃ ν : 𝓞 E, ν ≠ 0 ∧ ν • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem
  | exact _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem
  | (apply _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem ..)

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

section Step
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) (g : Matrix (Fin n) (Fin n) E)
    {L M : Submodule (𝓞 E) (Fin n → E)} (h : ∀ x ∈ L, g *ᵥ x ∈ M) {X : Fin n → E ⊗[F] R}
    (hX : X ∈ Formalism.UG.latS (F := F) R S L) :
    g.map (Formalism.UG.inclE (F := F) R) *ᵥ X ∈ Formalism.UG.latS (F := F) R S M := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    exact Submodule.subset_span ⟨_, h x hx, funext fun i => RingHom.map_mulVec _ g x i⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx

theorem mem_latS_mulLat (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) (γ : GL (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (X : Fin n → E ⊗[F] R) :
    X ∈ Formalism.UG.latS (F := F) R S (Formalism.L2.Forms.mulLat γ.1 L) ↔
      ((Formalism.UG.bc (Formalism.UG.inclE (F := F) R) γ)⁻¹).1 *ᵥ X ∈ Formalism.UG.latS (F := F) R S L := by
  constructor
  · intro hX
    rw [← map_inv]
    refine mulVec_mem_latS R S (γ⁻¹).1 ?_ hX
    rintro _ ⟨x, hx, rfl⟩
    show (γ⁻¹).1 *ᵥ (γ.1 *ᵥ x) ∈ L
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · intro hX
    have h := mulVec_mem_latS R S γ.1 (M := Formalism.L2.Forms.mulLat γ.1 L) (fun x hx => ⟨x, hx, rfl⟩) hX
    have e : γ.1.map (Formalism.UG.inclE (F := F) R) = (Formalism.UG.bc (Formalism.UG.inclE (F := F) R) γ).1 := rfl
    rwa [e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h

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

theorem locLat_of_adStep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (Lb lat lat' : Submodule (𝓞 E) (Fin n → E)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) (v w : HeightOneSpectrum (𝓞 F)), Module.Finite (𝓞 E) Lb → Module.Finite (𝓞 E) lat → Module.Finite (𝓞 E) lat' → (∀ κ ∈ U, ∀ X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb ↔ (κ : Matrix (Fin n) (Fin n) _) *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb) → (∀ X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lat ↔ (y⁻¹).1 *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb) → (∀ X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lat' ↔ (y'⁻¹).1 *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb) → Formalism.L2.Herm.AdStep σ J U y y' γ v → w ≠ v → ∀ z : Fin n → E ⊗[F] w.adicCompletion F, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w (Formalism.L2.Forms.mulLat γ.1 lat') ↔ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w lat := by
  intro F E _ _ _ _ _ σ n J U Lb lat lat' y y' γ v w hLb hl hl' hU hy hy' hS hw z
  obtain ⟨κ, hκ, η, -, hη, e⟩ := hS
  have hfin : Module.Finite (𝓞 E) (Formalism.L2.Forms.mulLat γ.1 lat') :=
    Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hl').map _)
  rw [mem_locLat_iff_adelic w _ hfin, mem_locLat_iff_adelic w _ hl, mem_latS_mulLat, hy, hy', hU κ hκ]
  set X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => Formalism.UG.P.afsplitIE w (z i) with hX
  have e1 : κ * y'⁻¹ * (Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ)⁻¹ = η⁻¹ * y⁻¹ := by
    rw [mul_assoc, ← _root_.mul_inv_rev, e]; group
  have e2 : (η⁻¹).1 *ᵥ ((y⁻¹).1 *ᵥ X) = (y⁻¹).1 *ᵥ X := by
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun p => ?_
    rw [map_sub, sub_eq_zero]
    refine (congrFun (GlobalTheory.LatticeStabLocal.prV_mulVec p _ _) i).trans ?_
    by_cases hp : p = w
    · subst hp
      have h1 : (η⁻¹).1.map (prV (E := E) p) = (Formalism.UG.bc (prV (E := E) p) η⁻¹).1 := rfl
      rw [h1, map_inv, hη p hw, inv_one, Units.val_one, Matrix.one_mulVec]
    · have h0 : (fun i => prV (E := E) p (((y⁻¹).1 *ᵥ X) i)) = 0 := by
        rw [GlobalTheory.LatticeStabLocal.prV_mulVec, show (fun i => prV (E := E) p (X i)) = 0 from
          funext fun i => Formalism.UG.P.afsplit_prV_IE_ne w p hp _, Matrix.mulVec_zero]
      rw [h0, Matrix.mulVec_zero]
      exact (congrFun h0 i).symm
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, e1, Units.val_mul,
    ← Matrix.mulVec_mulVec, e2]

end Step

theorem locP_le_of_le' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L N : Submodule R W} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx'⟩

theorem clsCrd_fin (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u i hi c) ∧
      Submodule.span D.host.E (clsCrd D u i hi c : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  letI := D.host.cmStar
  have h := D.clsLat_lat u i c
  refine ⟨Module.Finite.iff_fg.2 (h.fg.map _), ?_⟩
  have h2 := congrArg (Submodule.map (((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E))) h.span_eq_top
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
  exact h2

theorem mulLat_fin {E : Type} [Field E] [NumberField E] {n : ℕ} (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Module.Finite (𝓞 E) L) (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Module.Finite (𝓞 E) (Formalism.L2.Forms.mulLat γ.1 L) ∧
      Submodule.span E (Formalism.L2.Forms.mulLat γ.1 L : Set (Fin n → E)) = ⊤ := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hL).map _), ?_⟩
  have e : (Formalism.L2.Forms.mulLat γ.1 L : Set (Fin n → E)) = (Matrix.mulVecLin γ.1) '' (L : Set (Fin n → E)) := rfl
  rw [e, ← Submodule.map_span, hs, Submodule.map_top, LinearMap.range_eq_top]
  intro z
  refine ⟨((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ z, ?_⟩
  simp [Matrix.mulVec_mulVec]

theorem stepLevel_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (lev : Formalism.L2.Forms.StepLevel F E σ J T f bad) (κ) (hκ : κ ∈ lev.U)
    (X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lev.Lb ↔
      (κ : Matrix (Fin n) (Fin n) _) *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lev.Lb := by
  haveI := lev.Lb_fin
  have h : κ ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lev.Lb) := by
    refine (GlobalTheory.LatticeStabLocal.mem_stabGL_adele_iff lev.Lb κ).2 fun v => ?_
    exact (Subgroup.mem_inf.1 (lev.Uloc_lev v (((lev.U_eq κ).1 hκ).2 v))).2
  exact h X

theorem locP_le_of_locLat_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Fin n → E)) (hBf : Module.Finite (𝓞 E) B)
    (hBs : Submodule.span E (B : Set (Fin n → E)) = ⊤)
    (hAB : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 F)) A → z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 F)) B) :
    Formalism.HermitianLatticesTheory.localization₂ q.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ q.asIdeal B :=
  locP_le_of_le' _ fun x hx =>
    mem_localization_of_mem_localLattice F E n _ B hBf hBs x (hAB _ (Submodule.subset_span ⟨x, hx, rfl⟩)) q rfl

set_option maxHeartbeats 4000000 in

theorem sameoff_gen {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F))
    (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (hAd : AdC T i hi c c' γ v)
    (q : HeightOneSpectrum (𝓞 D.host.E)) (hq : q.under (𝓞 D.host.F) ≠ v) :
    Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (Formalism.L2.Forms.mulLat γ.1 (clsCrd D u i hi c')) =
      Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd D u i hi c) := by
  obtain ⟨f1, s1⟩ := clsCrd_fin D u i hi c
  obtain ⟨f2, s2⟩ := clsCrd_fin D u i hi c'
  obtain ⟨f3, s3⟩ := mulLat_fin γ _ f2 s2
  have key : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 D.host.F)) (Formalism.L2.Forms.mulLat γ.1 (clsCrd D u i hi c')) ↔
      z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 D.host.F)) (clsCrd D u i hi c) := by
    by_cases h0 : i = 0 ∨ i = D.R.m
    · have hS := hAd.1 h0
      exact locLat_of_adStep _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.cls i hi h0).lev.Lb_fin f1 f2
        (fun κ hκ X => stepLevel_stab _ κ hκ X) ((T.cls i hi h0).y_lat c) ((T.cls i hi h0).y_lat c') hS hq
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ D.R.m := by omega
      obtain ⟨hβ, hS⟩ := hAd.2 h1 h2
      exact locLat_of_adStep _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.ch i h1 h2 (chOf i c)).lev.Lb_fin f1 f2
        (fun κ hκ X => stepLevel_stab _ κ hκ X) ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩)
        ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c', hβ⟩) hS hq
  exact le_antisymm (locP_le_of_locLat_le q _ _ f1 s1 fun z hz => (key z).1 hz)
    (locP_le_of_locLat_le q _ _ f3 s3 fun z hz => (key z).2 hz)

set_option maxHeartbeats 4000000 in

theorem use₆ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → ∀ q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 → Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (Formalism.L2.Forms.mulLat γ.1 (clsCrd (I.rec7 l Z) u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd (I.rec7 l Z) u i hi c) := by
  intro B X I _ _ l Z H F _ _ u i hi v c c' γ hAd q hq
  exact sameoff_gen (F u) i hi _ c c' γ hAd q hq

end GlobalTheory.Mem.Col2.SameOff

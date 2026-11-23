import Formalism.LocalToGlobal.Columns.TiedMvA

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hxm_hform_mulVec {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J g : Matrix (Fin n) (Fin n) R)
    (h : cT σ g * J * g = J) (x y : Fin n → R) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ (J' : Matrix (Fin n) (Fin n) R) (a b : Fin n → R), hform σ J' a b = (fun i => σ (a i)) ⬝ᵥ (J' *ᵥ b) := by
    intro J' a b
    unfold hform dotProduct mulVec dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    unfold mulVec dotProduct
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  rw [key, key, hs, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ g * J * g) *ᵥ y) = _
  rw [h]

variable {D : ColRec}

def hxG (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨((CF.crdN D i hi).trans (glEquiv γ.1)).trans (CF.crdN D i hi).symm, by
    intro x y
    rw [hx_hform i hi, hx_hform i hi x y]
    show hform _ _ (CF.crdN D i hi ((CF.crdN D i hi).symm (γ.1.1 *ᵥ CF.crdN D i hi x)))
      (CF.crdN D i hi ((CF.crdN D i hi).symm (γ.1.1 *ᵥ CF.crdN D i hi y))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hxm_hform_mulVec _ _ _ γ.2 _ _⟩

theorem hxG_crd (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((hxG i hi γ).1 x) = γ.1.1 *ᵥ CF.crdN D i hi x :=
  (CF.crdN D i hi).apply_symm_apply _

abbrev hxMap (i : ℕ) (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  M.map ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

theorem hxm_map_inj {i : ℕ} (hi : i ≤ D.R.m) {M M' : Submodule (𝓞 D.host.E) (D.sp.X i).V} (h : hxMap i hi M = hxMap i hi M') :
    M = M' := by
  ext x
  rw [← hx_mem_map hi M x, ← hx_mem_map hi M' x]
  show _ ∈ hxMap i hi M ↔ _ ∈ hxMap i hi M'
  rw [h]

theorem hxm_map_gmap (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    hxMap i hi (gmap (hxG i hi γ).1 M) = Formalism.L2.Forms.mulLat γ.1.1 (hxMap i hi M) := by
  unfold hxMap gmap Formalism.L2.Forms.mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact hxG_crd i hi γ x

theorem hxm_map_locP (i : ℕ) (hi : i ≤ D.R.m) (p : Ideal (𝓞 D.host.E)) [p.IsPrime] (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    hxMap i hi (localization₂ p M) = localization₂ p (hxMap i hi M) := by
  ext t
  constructor
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    refine ⟨s, hs, ⟨s • x, hx, ?_⟩⟩
    exact ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)).map_smul s x
  · rintro ⟨s, hs, ⟨x, hx, e⟩⟩
    refine ⟨(CF.crdN D i hi).symm t, ⟨s, hs, ?_⟩, (CF.crdN D i hi).apply_symm_apply t⟩
    have e2 : s • (CF.crdN D i hi).symm t = x := by
      apply (CF.crdN D i hi).injective
      have e3 := ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
        (𝓞 D.host.E)).map_smul s ((CF.crdN D i hi).symm t)
      refine Eq.trans e3 ?_
      show s • CF.crdN D i hi ((CF.crdN D i hi).symm t) = _
      rw [LinearEquiv.apply_symm_apply]
      exact e.symm
    rw [e2]
    exact hx

theorem hxm_crd_frame (i : ℕ) (hi : i ≤ D.R.m) (b : Fin (D.sp.X i).rank) :
    CF.crdN D i hi ((D.sp.X i).frame b) = Pi.single (finCongr (CF.rankN D i hi) b) (1 : D.host.E) := by
  funext j
  show (D.sp.X i).frame.equivFun ((D.sp.X i).frame b) ((finCongr (CF.rankN D i hi)).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

theorem hxG_toGLb (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) :
    Formalism.L2.Herm.toGLb (D.sp.X i).frame (hxG i hi γ).1 = Formalism.L2.Forms.reGL (CF.rankN D i hi).symm _ γ.1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  show LinearMap.toMatrixAlgEquiv (D.sp.X i).frame (((hxG i hi γ).1 : (D.sp.X i).V ≃ₗ[D.host.E] (D.sp.X i).V) :
    (D.sp.X i).V →ₗ[D.host.E] (D.sp.X i).V) a b = γ.1.1 (finCongr (CF.rankN D i hi) a) (finCongr (CF.rankN D i hi) b)
  rw [LinearMap.toMatrixAlgEquiv_apply]
  have h1 : (D.sp.X i).frame.repr ((hxG i hi γ).1 ((D.sp.X i).frame b)) a =
      CF.crdN D i hi ((hxG i hi γ).1 ((D.sp.X i).frame b)) (finCongr (CF.rankN D i hi) a) := by
    show _ = (D.sp.X i).frame.equivFun _ ((finCongr (CF.rankN D i hi)).symm (finCongr (CF.rankN D i hi) a))
    rw [Equiv.symm_apply_apply]
    rfl
  refine Eq.trans h1 ?_
  rw [hxG_crd, hxm_crd_frame, Matrix.mulVec_single_one]
  rfl

theorem hxG_toGLb0 (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D 0 (Nat.zero_le _))) :
    Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (hxG 0 (Nat.zero_le _) γ).1 =
      Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ γ.1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  show LinearMap.toMatrixAlgEquiv ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0))
    (((hxG 0 (Nat.zero_le _) γ).1 : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V) a b =
      γ.1.1 (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) a) (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) b)
  rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindex_apply, Basis.repr_reindex_apply]
  have h1 : ∀ x : (D.sp.X 0).V, (D.sp.X 0).frame.repr x ((finCongr D.sp.rank0).symm a) =
      CF.crdN D 0 (Nat.zero_le _) x (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) a) := fun x => rfl
  refine Eq.trans (h1 _) (Eq.trans (congrFun (hxG_crd 0 (Nat.zero_le _) γ ((D.sp.X 0).frame ((finCongr D.sp.rank0).symm b)))
    (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) a)) ?_)
  rw [hxm_crd_frame, Matrix.mulVec_single_one]
  rfl

theorem localization_map_eq_of_transport {i : ℕ} (hi : i ≤ D.R.m) (p : Ideal (𝓞 D.host.E)) [p.IsPrime]
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) {M M' : Submodule (𝓞 D.host.E) (D.sp.X i).V}
    (h : localization₂ p (Formalism.L2.Forms.mulLat γ.1.1 (hxMap i hi M)) = localization₂ p (hxMap i hi M')) :
    localization₂ p (gmap (hxG i hi γ).1 M) = localization₂ p M' := by
  apply hxm_map_inj hi
  rw [hxm_map_locP, hxm_map_locP, hxm_map_gmap]
  exact h

theorem hxm_sameOff {i : ℕ} (hi : i ≤ D.R.m) (p : Ideal (𝓞 D.host.E))
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) {M M' : Submodule (𝓞 D.host.E) (D.sp.X i).V}
    (h : SameOffC p (Formalism.L2.Forms.mulLat γ.1.1 (hxMap i hi M)) (hxMap i hi M')) :
    Formalism.L2.Herm.SameOff (S := D.sp.X i) p (gmap (hxG i hi γ).1 M) M' := fun q hq h1 h2 => by
  have := hq.isPrime
  exact localization_map_eq_of_transport hi q γ (h q hq h1 h2)

theorem hxm_map_sup_span {i : ℕ} (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (t : D.host.E) (y : (D.sp.X i).V) :
    hxMap i hi (M ⊔ Submodule.span (𝓞 D.host.E) {t • y}) =
      hxMap i hi M ⊔ Submodule.span (𝓞 D.host.E) {t • CF.crdN D i hi y} := by
  unfold hxMap
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  congr 3
  exact map_smul (CF.crdN D i hi) t y

theorem hxm_nat_smul {i : ℕ} (hi : i ≤ D.R.m) (T : ℕ) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((T : D.host.E) • x) = ((T : ℕ) : 𝓞 D.host.E) • CF.crdN D i hi x := by
  rw [map_smul, Algebra.smul_def', map_natCast]
  rfl

theorem hxm_Ld (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    hxMap i hi (CH.Ld D u i c) = CF.Ld D u i hi c := (hx_Ld_eq u i hi c).symm

variable {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

set_option maxHeartbeats 4000000 in

theorem hxm_up (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c))
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (p : (D.fm u).lv i v c)
    (h : SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c p))) (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.Ld D u i hi ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (hxLd i hi c y).1}) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c p)))
        (hz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ z.1) ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c p))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))) :
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).up i v c p))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (CH.Ld D u i ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).up i v c p))
        (hz : ((D.mem u).A.T : D.host.E) • (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).up i v c p))
        (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨hxm_sameOff hi _ γ h1, localization_map_eq_of_transport hi _ γ ?_, localization_map_eq_of_transport hi _ γ ?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · rw [hxm_Ld]; exact h2
  · rw [hxm_map_sup_span, hxm_Ld, hxm_Ld]; exact h3
  · have e : CF.crdN D i hi (((D.mem u).A.T : D.host.E) • (hxG i hi γ).1 z.1) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (hxLd i hi _ z).1) := by
      rw [hxm_nat_smul, hxG_crd]; rfl
    have hz' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (hxLd i hi _ z).1) ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h4 (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h5 v' hv' (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm

set_option maxHeartbeats 4000000 in

theorem hxm_dn (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c))
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (h : SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).dn i v c g))) (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.clsCrd D u i hi c) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Lk A i hi v c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = g ((P i hi).prk v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))) :
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (CH.Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Lk D u (A.Pv v) i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = g (hxPrk A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hxm_sameOff hi _ γ h1, localization_map_eq_of_transport hi _ γ ?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · rw [hxm_Ld]; exact h2
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Lk A i hi v c := by
      rw [← e]; exact (hx_mem_Lk A i hi v c _).2 hz
    rw [hxPr_eq A P i hi, hxPrk_eq A P i hi, h3 (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h4 v' hv' (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm

set_option maxHeartbeats 4000000 in

theorem hxm_dil (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (h : Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).dil i v a c)) = CF.clsCrd D u i hi c ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))) :
    Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hxm_map_inj hi ?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · rw [hxm_map_gmap]; exact h1
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h2 (hxLd i hi _ z) hz']
    congr 3
    exact Subtype.ext e.symm
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h3 v' hv' (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm

variable {A P} (M : AtTMovesC A P)

open Classical in

def AtTMovesC.upS (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c)) : CH.GX D i :=
  if hi : i ≤ D.R.m then hxG i hi (M.upG i hi v c (hxLd i hi c y)) else 1

open Classical in

def AtTMovesC.dnS (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) : CH.GX D i :=
  if hi : i ≤ D.R.m then hxG i hi (M.dnG i hi v c g) else 1

open Classical in

def AtTMovesC.dilS (i : ℕ) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) : CH.GX D i :=
  if hi : i ≤ D.R.m then hxG i hi (M.dilG i hi v a c) else 1

theorem AtTMovesC.upS_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c)) :
    M.upS i v c y = hxG i hi (M.upG i hi v c (hxLd i hi c y)) := dif_pos hi

theorem AtTMovesC.dnS_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) : M.dnS i v c g = hxG i hi (M.dnG i hi v c g) := dif_pos hi

theorem AtTMovesC.dilS_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) :
    M.dilS i v a c = hxG i hi (M.dilG i hi v a c) := dif_pos hi

set_option maxHeartbeats 4000000 in

def AtTMovesC.toMoves : AtTMoves A P where
  upG := M.upS
  up_tie := fun i hi v c y hy => by
    have hy' : (D.fm u).fv i v c ((P i hi).pr v c (hxLd i hi c y)) = 1 := by
      rw [← hxPr_eq A P i hi]; exact hy
    have h := M.up_tie i hi v c (hxLd i hi c y) hy'
    rw [← hxPr_eq A P i hi v c y] at h
    rw [M.upS_eq i hi]
    exact hxm_up A P i hi v c y _ _ h
  dnG := M.dnS
  dn_tie := fun i hi v c g hg => by
    rw [M.dnS_eq i hi]
    exact hxm_dn A P i hi v c g _ (M.dn_tie i hi v c g hg)
  dilG := M.dilS
  dil_tie := fun i hi v a c => by
    rw [M.dilS_eq i hi]
    exact hxm_dil A P i hi v a c _ (M.dil_tie i hi v a c)

end Formalism.L2.Col

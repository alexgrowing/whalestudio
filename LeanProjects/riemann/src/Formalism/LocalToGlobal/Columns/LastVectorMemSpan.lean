import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.HermitianForms.BothLemmas

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

theorem hqG_crd (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((hqG i hi g).1 x) = (g.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ CF.crdN D i hi x :=
  hqLin_crd _ _ g.1 x

theorem hqG_re (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) :
    Formalism.L2.Forms.reGL (CF.rankN D i hi) D.host.E (Formalism.L2.Herm.toGLb (D.sp.X i).frame (hqG i hi g).1) = g.1 :=
  hqLin_re _ _ g.1

theorem hqG_gmap (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    (gmap (hqG i hi g).1 L).map
        ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) =
      Formalism.L2.Forms.mulLat (g.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) (L.map
        ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) := by
  unfold gmap Formalism.L2.Forms.mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact hqG_crd i hi g x

theorem hq_map_inj (i : ℕ) (hi : i ≤ D.R.m) : Function.Injective (Submodule.map
    ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) :=
  Submodule.map_injective_of_injective (CF.crdN D i hi).injective

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

def hqLatP (K : CF.ClsPTied u) (c : (D.fm u).clsP) : Submodule (𝓞 D.host.E) D.sp.X'.V :=
  (K.lat c).map (((CF.crdP D).symm : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V).restrictScalars (𝓞 D.host.E))

theorem hqLatP_crd (K : CF.ClsPTied u) (c : (D.fm u).clsP) :
    K.lat c = (hqLatP K c).map
      ((CF.crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  unfold hqLatP
  rw [← Submodule.map_comp]
  symm
  convert Submodule.map_id _
  ext x j
  simp

variable (T : CF.TilTied u A K (P D.R.m le_rfl))

def lastSpaceVector : (D.sp.X D.R.m).V := (CF.crdN D D.R.m le_rfl).symm T.z0

theorem lastVector_coords : T.z0 = CF.crdN D D.R.m le_rfl (lastSpaceVector T) := ((CF.crdN D D.R.m le_rfl).apply_symm_apply T.z0).symm

theorem lastVector_mem_span : lastSpaceVector T ∈ Submodule.span D.host.E {D.sp.z} := by
  obtain ⟨a, ha⟩ := T.lastCoordinateUniformizerVector_spans_orthogonal_line
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  unfold lastSpaceVector
  rw [LinearEquiv.eq_symm_apply, map_smul, ha]
  rfl

theorem lastVector_norm : (D.sp.X D.R.m).hT (lastSpaceVector T) (lastSpaceVector T) = ((D.mem u).A.T : D.host.E) := by
  rw [hx_hform D.R.m le_rfl, ← lastVector_coords]
  exact T.hermitianForm_lastCoordinateUniformizerVector_self

def hqTilG (c : (D.fm u).clsP) : CH.GX D D.R.m := hqG D.R.m le_rfl (T.ga c)

set_option maxHeartbeats 1000000 in
theorem hq_til_lat (c : (D.fm u).clsP) :
    gmap (hqTilG T c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (hqLatP K c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {lastSpaceVector T} := by
  apply hq_map_inj D.R.m le_rfl
  rw [hqTilG, hqG_gmap, ← hx_clsCrd, T.til_lat c, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  congr 1
  · unfold hqLatP
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  · congr 2
    exact lastVector_coords T

set_option maxHeartbeats 1000000 in
theorem hq_til_fv (c : (D.fm u).clsP) (v : (D.mem u).A.vT) (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E)
    (ha : (a : D.host.E) = (D.sp.X D.R.m).hT (lastSpaceVector T) ((hqTilG T c).1 (z : (D.sp.X D.R.m).V))) :
    (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a := by
  rw [hxPr_eq A P D.R.m le_rfl]
  refine T.til_fv v c (hxLd D.R.m le_rfl _ z) a ?_
  rw [ha, hx_hform D.R.m le_rfl, ← lastVector_coords, hqTilG, hqG_crd]
  rfl

set_option maxHeartbeats 4000000 in

def xpOf (levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0))
    (clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ (hqLatP K)) :
    AtTXp A P where
  lattice₂ := hqLatP K
  levP := levP
  clsP := clsP
  z0 := lastSpaceVector T
  cocycle_zero_mem_invariants := lastVector_mem_span T
  hermitianForm_lastCoordinateUniformizerVector_self := lastVector_norm T
  tilG := hqTilG T
  til_tie := fun c => ⟨hq_til_lat T c, fun v z a ha => hq_til_fv T c v z a ha⟩

end Formalism.L2.Col

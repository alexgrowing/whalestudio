import Formalism.LocalToGlobal.GlobalTheory.MemCompanion
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfFlags
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.Herm

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem std_coords (S : HSpace E) (hS : IsStd S) (N : ℕ) (hN : S.rank = N) :
    ∃ co : S.V ≃ₗ[E] (Fin N → E), ∀ x y, stdH E N (co x) (co y) = S.hT x y := by
  obtain ⟨b, hb, -⟩ := hS
  refine ⟨b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr hN).symm), fun x y => ?_⟩
  have h1 : S.hT x y = ∑ a, star (b.repr x a) * b.repr y a := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hb]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp only [if_true, mul_one]
      rw [mul_comm]; rfl
    · intro a' _ ha'
      rw [if_neg ha', mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [h1]
  unfold stdH
  refine Fintype.sum_equiv (finCongr hN).symm _ _ (fun j => ?_)
  simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]

variable {hc : CMData F E} {S : HSpace E}

theorem step_of (K : Coord hc S n) {N : ℕ} (co : S.V ≃ₗ[E] (Fin N → E))
    (hco : ∀ x y, stdH E N (co x) (co y) = S.hT x y) {cls : Type} (lat : cls → Submodule (𝓞 E) S.V)
    (hlat : ∀ c, Submodule.IsLattice E (lat c)) {Λb : Submodule (𝓞 E) (n → E)} (hΛb : IsLat Λb)
    (y : cls → GL n 𝒜) (hy : ∀ c, y c ∈ UPts hc.sig K.J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ c (u : n → 𝒜), u ∈ hat F (K.lat (lat c)) ↔ ((y c)⁻¹ : GL n 𝒜).1 *ᵥ u ∈ hat F Λb)
    {a : 𝓞 E} (ha : a ≠ 0) (hbase : Λb ⊔ Ideal.span {a} • dl hc.sig K.J Λb = K.lat S.L0) :
    ∃ L0 : SDLat E N, (∀ y, co y ∈ L0.1 ↔ y ∈ S.L0) ∧ ∀ c, ∃ Ln : SDLat E N,
      (∀ z, co z ∈ Ln.1 ↔ ∃ x ∈ lat c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT (lat c), z = x + (a : E) • b) ∧
      ∃ g' ∈ UstdAf hc N, Carries g' L0.1 Ln.1 ∧ ∃ x : unitaryOneFiniteAdeles hc, IsDetOf hc x g' ∧
        Matrix.GeneralLinearGroup.det (x : GL (Fin 1) 𝒜) = Matrix.GeneralLinearGroup.det (y c) := by
  refine ⟨K.StandardHermitianLattice co hco, fun z => K.mem_mapQ_lat co S.L0 z, fun c => ?_⟩
  obtain ⟨Ln, hmem, g', hg', hcar, hdet⟩ := K.main co hco (hlat c) hΛb (y c) (hy c) (hyl c) ha hbase
  obtain ⟨x, hx, hxd⟩ := exists_unitary_one_det_eq hc.sig g' hg'
  exact ⟨Ln, hmem, g', hg', hcar, ⟨x, hx⟩, hxd, hxd.trans hdet⟩

end Gen

end Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory.Comp NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def conjInt (D : D7) (x : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨D.host.conj (x : D.host.E), (RingOfIntegers.isIntegral_coe x).map (D.host.conj.toAlgHom.restrictScalars ℤ)⟩

theorem piU_ne_zero {D : D7} {H : HermCols D} (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (u : D.what₂.Word) :
    conjInt D (aT u).piU ≠ 0 := by
  intro h
  have h1 := (aT u).piU_norm
  have h2 : D.host.conj ((aT u).piU : D.host.E) = 0 := congrArg Subtype.val h
  rw [h2, mul_zero] at h1
  exact (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero) h1.symm

set_option maxHeartbeats 1000000 in

theorem base_lattice_convention_of_hermitian {D : D7} (X : FullTied D) (u : D.what₂.Word) : AdmBRest D u (X.atT u).piU := by
  intro i hi
  set pb := conjInt D (X.atT u).piU with hpb
  have hpb0 : pb ≠ 0 := piU_ne_zero X.atT u
  have hpbE : (pb : D.host.E) = D.host.conj ((X.atT u).piU : D.host.E) := rfl
  obtain ⟨co, hco⟩ := std_coords (D.sp.X i) (X.std.1 i hi) (D.R.N i) (D.sp.X_rank i hi)
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · let K : Coord D.sp.cm (D.sp.X 0) (Fin D.R.k) := ⟨D.sp.crd0, D.sp.gram0, D.sp.hermitianForm_base_coordinates⟩
    have hΛ : IsLat (X.base.lev0 u).Lb := ⟨(X.base.lev0 u).Lb_fin, (X.base.lev0 u).Lb_span⟩
    have hy : ∀ c, ((X.base.lev0 u).y c : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∈
        Formalism.UG.UPts D.sp.cm.sig K.J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun c => ((X.base.lev0 u).y c).2
    have hyl : ∀ c (v : Fin D.R.k → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        v ∈ hat D.host.F (K.lat (D.clsLat u 0 c)) ↔
          (((X.base.lev0 u).y c : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹ :
            GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 *ᵥ v ∈
            hat D.host.F (X.base.lev0 u).Lb := fun c v => (X.base.lev0 u).y_lat c v
    have hb : (X.base.lev0 u).Lb ⊔ Ideal.span {pb} • dl D.sp.cm.sig K.J (X.base.lev0 u).Lb = K.lat (D.sp.X 0).L0 :=
      (X.baseL u pb hpbE).1
    obtain ⟨L0, hL0, hc⟩ := step_of K co hco (D.clsLat u 0) (D.clsLat_lat u 0) hΛ
      (fun c => ((X.base.lev0 u).y c : GL (Fin D.R.k) _)) (fun c => by exact hy c) (fun c v => by exact hyl c v) hpb0
      (by exact hb)
    refine ⟨co, L0, hco, hL0, fun c => ?_⟩
    obtain ⟨Ln, hmem, g', hg', hcar, x, hx, hxd⟩ := hc c
    refine ⟨Ln, fun z => by rw [hmem z, hpbE], ?_⟩
    rw [X.base.det0 u c x hxd, X.relDet _ L0 Ln g' hg' hcar x hx]
  · let K : Coord D.sp.cm (D.sp.X i) (Fin (D.sp.X i).rank) := ⟨crd (D.sp.X i), (D.sp.X i).gram, hT_crd D.sp.cm (D.sp.X i)⟩
    have hΛ : IsLat (X.base.lev u i h1 hi).Lb := ⟨(X.base.lev u i h1 hi).Lb_fin, (X.base.lev u i h1 hi).Lb_span⟩
    have hy : ∀ c, ((X.base.cls u i h1 hi).y c : GL (Fin (D.sp.X i).rank) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∈
        Formalism.UG.UPts D.sp.cm.sig K.J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun c => ((X.base.cls u i h1 hi).y c).2
    have hyl : ∀ c (v : Fin (D.sp.X i).rank → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        v ∈ hat D.host.F (K.lat (D.clsLat u i c)) ↔
          (((X.base.cls u i h1 hi).y c : GL (Fin (D.sp.X i).rank) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹ :
            GL (Fin (D.sp.X i).rank) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 *ᵥ v ∈
            hat D.host.F (X.base.lev u i h1 hi).Lb := fun c v => (X.base.cls u i h1 hi).y_lat c v
    have hb : (X.base.lev u i h1 hi).Lb ⊔ Ideal.span {pb} • dl D.sp.cm.sig K.J (X.base.lev u i h1 hi).Lb =
        K.lat (D.sp.X i).L0 := (X.baseL u pb hpbE).2 i h1 hi
    obtain ⟨L0, hL0, hc⟩ := step_of K co hco (D.clsLat u i) (D.clsLat_lat u i) hΛ
      (fun c => ((X.base.cls u i h1 hi).y c : GL (Fin (D.sp.X i).rank) _)) (fun c => by exact hy c) (fun c v => by exact hyl c v) hpb0
      (by exact hb)
    refine ⟨co, L0, hco, hL0, fun c => ?_⟩
    obtain ⟨Ln, hmem, g', hg', hcar, x, hx, hxd⟩ := hc c
    refine ⟨Ln, fun z => by rw [hmem z, hpbE], ?_⟩
    rw [X.base.detI u i h1 hi c x hxd, X.relDet _ L0 Ln g' hg' hcar x hx]

end Formalism.L2.GlobalTheoryTheory

end

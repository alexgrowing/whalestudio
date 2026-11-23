import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DualQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rlv_dualQ {n : ℕ} (σ : E →ₐ[F] E) (hσσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hH : ∀ u w, hform (σ : E →+* E) J w u = σ (hform (σ : E →+* E) J u w))
    (g : Matrix (Fin n) (Fin n) E) (hg : cT (σ : E →+* E) g * J * g = J)
    (P : Ideal (𝓞 E)) [P.IsPrime] {A B : Submodule (𝓞 E) (Fin n → E)}
    (hBfg : (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B).FG)
    (hBB : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ B)
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ Formalism.HermitianLatticesTheory.localization₂ P (mulLat g (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J A))) :
    Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) (mulLat g A) ≤
      Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) B := by
  classical
  have hP1 : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  intro x hx
  obtain ⟨t0, ht0, hx0⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 hx0
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hax
  have key : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, ∃ s : 𝓞 E, s ∉ P ∧
      (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (rlv_mem_locP _ _ _).1 (hP ((rlv_mem_locP _ _ _).2 ⟨1, hP1, by rw [one_smul]; exact hy⟩))
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hsy
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hwy
    refine ⟨s, hs, ?_⟩
    have e1 : (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y = hform (σ : E →+* E) J (g *ᵥ a) (s • y) := by
      rw [← algebraMap_smul E s y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
    rw [e1, ← hwy, Formalism.UG.P.hform_mulVec, hg]
    exact (Formalism.L2.GlobalTheoryTheory.Comp.mem_dl σ J A w).1 hw a ha
  choose! sf hsfP hsf using key
  obtain ⟨S, hS⟩ := hBfg
  have hSsub : ∀ y ∈ S, y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B := fun y hy => hS ▸ Submodule.subset_span hy
  set s : 𝓞 E := ∏ y ∈ S, sf y with hsdef
  have hsP : s ∉ P := by
    rw [hsdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨y, hy, hyP⟩
    exact hsfP y (hSsub y hy) hyP
  have hgen : ∀ y ∈ S, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [hsdef, ← Finset.mul_prod_erase S sf hy]
    obtain ⟨r, hr⟩ := hsf y (hSsub y hy)
    refine ⟨(∏ z ∈ S.erase y, sf z) * r, ?_⟩
    rw [map_mul, hr]
    push_cast
    ring
  have hall : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_zero_right, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_add_right, mul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul E r y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
      obtain ⟨q, hq⟩ := hy
      exact ⟨r * q, by rw [map_mul, hq]; ring⟩
  set s' : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) s with hs'def
  have hs'E : (s' : E) = σ (s : E) := rfl
  have hmem : s' • (g *ᵥ a) ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) := by
    apply Submodule.subset_span
    intro y hy
    have e2 : hform (σ : E →+* E) J y (s' • (g *ᵥ a)) = σ ((s : E) * hform (σ : E →+* E) J (g *ᵥ a) y) := by
      rw [← algebraMap_smul E s' (g *ᵥ a), Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right, hH, map_mul]
      rfl
    rw [e2]
    obtain ⟨q, hq⟩ := hall y hy
    exact ⟨RingOfIntegers.mapRingHom (σ : E →+* E) q, by rw [← hq]; rfl⟩
  refine (rlv_mem_locP _ _ _).2 ⟨s' * t0, ?_, ?_⟩
  · intro hm
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hm) with h1 | h1
    · apply hsP
      have : RingOfIntegers.mapRingHom (σ : E →+* E) s' = s := by
        apply RingOfIntegers.ext
        show σ (σ (s : E)) = (s : E)
        exact hσσ _
      rw [← this]
      exact h1
    · exact ht0 h1
  · rw [mul_smul, ← hax]
    exact hBB hmem

end DualQ

section TiedQ

variable {D : D7} {u : D.what₂.Word}

theorem rlv_sig_sig (x : D.host.E) : sigD D (sigD D x) = x := by
  rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]

set_option maxHeartbeats 2000000 in

theorem rlv_coordFacts (i : ℕ) (hi : i ≤ D.R.m) :
    (∀ c, Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) =
      clsCrd D u i hi c) ∧
    (∀ c, (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)).FG) ∧
    (∀ a b, hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) b a =
      sigD D (hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b)) := by
  letI := D.host.cmStar
  set κ : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) with hκ
  have hform_eq : ∀ x y, (D.sp.X i).hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (κ x) (κ y) := by
    intro x y
    have hx : (D.sp.X i).hT x y = ∑ a, ∑ b, star ((D.sp.X i).frame.repr x a) * (D.sp.X i).gram a b *
        (D.sp.X i).frame.repr y b := by
      conv_lhs => rw [← (D.sp.X i).frame.sum_repr x, ← (D.sp.X i).frame.sum_repr y]
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, HSpace.gram, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [RingHom.id_apply]
      ring
    rw [hx]
    unfold hform
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [gramN, hκ, CMData.sig, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, starRingEnd_apply]
  let K : Formalism.L2.GlobalTheoryTheory.Comp.Coord D.sp.cm (D.sp.X i) (Fin (D.R.N i)) := ⟨κ, gramN D i hi, hform_eq⟩
  refine ⟨fun c => ?_, fun c => ?_, fun a b => ?_⟩
  · have h1 := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (D.sp.X i).V (D.sp.X i).hT (D.sp.X i).herm (D.sp.X i).nondeg
      Formalism.L2.GlobalTheoryTheory.Comp.star_int (D.clsLat u i c) (D.clsLat_lat u i c)
    have e1 := K.lat_dual (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))
    have e2 := K.lat_dual (D.clsLat u i c)
    rw [h1.2.1, e2] at e1
    exact e1.symm
  · have h1 := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (D.sp.X i).V (D.sp.X i).hT (D.sp.X i).herm (D.sp.X i).nondeg
      Formalism.L2.GlobalTheoryTheory.Comp.star_int (D.clsLat u i c) (D.clsLat_lat u i c)
    have e2 := K.lat_dual (D.clsLat u i c)
    have h3 := K.isLat_lat h1.1
    rw [e2] at h3
    exact Module.Finite.iff_fg.1 h3.1
  · have h := (D.sp.X i).herm.eq (κ.symm a) (κ.symm b)
    rw [hform_eq, hform_eq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

set_option maxHeartbeats 2000000 in

theorem rlv_Q_of_dualP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E) (hgU : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E) (Ld D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c)) :
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi c) := by
  obtain ⟨hdd, hfg, hH⟩ := rlv_coordFacts (D := D) (u := u) i hi
  have hgU' : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) := inv_mem hgU
  have hg1 : cT (sigD D : D.host.E →+* D.host.E) (g : Matrix _ _ D.host.E) * gramN D i hi * (g : Matrix _ _ D.host.E) =
      gramN D i hi := hgU
  have hg1' : cT (sigD D : D.host.E →+* D.host.E) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) * gramN D i hi *
      ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) = gramN D i hi := hgU'
  have hPd' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) ≤
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) := hPd.ge
  have hPd'' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) ≤
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) := hPd.le
  apply le_antisymm
  · exact rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1 (Tf.atT.Pv v) (hfg c) (hdd c).le hPd'
  · have h1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2)) ≤
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E)
          (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c))) := by
      have := rlv_locP_mulLat_le (Tf.atT.Pv v) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) hPd''
      rwa [rlv_mulLat_inv] at this
    have h2 := rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1' (Tf.atT.Pv v) (hfg c2) (hdd c2).le h1
    have h3 := rlv_locP_mulLat_le (rlvQ Tf.atT v) (g : Matrix _ _ D.host.E) h2
    have e3 := rlv_mulLat_inv g⁻¹ (clsCrd D u i hi c)
    rw [inv_inv] at e3
    rw [e3] at h3
    exact h3

end TiedQ

section TiedW

variable {D : D7} {u : D.what₂.Word}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def RUpLocW (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) = (Tf.lv i hi).pr v c z ∧
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1 =
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))))
          (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (((D.fm u).fv i v c).comp e.toLinearMap)
              ((Tf.lv i hi).prk v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ⟨_, hx⟩)) →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1 * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) ∧
      bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ.1 * γ'.1) *
        ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1) ∈ stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def RDnLocW (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      ∀ (z : ↥(Ld D u i hi ((D.fm u).dn i v c g))),
        (Tf.lv i hi).pr v ((D.fm u).dn i v c g) z = e.symm ((D.fm u).te i v c) →
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1 =
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g)) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g) ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi ((D.fm u).dn i v c g)),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v ((D.fm u).dn i v c g) ⟨_, hx⟩)) →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ'.1 * γ.1).1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) ∧
      bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ'.1 * γ.1) *
        ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1) ∈ stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem raising_local_v_of_local_w (Tf : FormsTied D u) (h : RUpLocW Tf) : RUpLocV Tf := by
  intro i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  obtain ⟨e, he1, he2⟩ := h i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  refine ⟨e, he1, fun γ' η' κ' hsup' hrel' hl1' hfun' => ?_⟩
  obtain ⟨hP, hF⟩ := he2 γ' η' κ' hsup' hrel' hl1' hfun'
  exact ⟨hP, rlv_Q_of_dualP Tf i hi v c _ (γ.1 * γ'.1) (mul_mem γ.2 γ'.2)
    (rlv_upDn_dualP Tf i hi v c _ _ γ γ' hl1 hl1'), hF⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem lowering_local_v_of_local_w (Tf : FormsTied D u) (h : RDnLocW Tf) : RDnLocV Tf := by
  intro i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  obtain ⟨e, he1, he2⟩ := h i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  refine ⟨e, he1, fun z hz γ η κ hsup hrel hl1 hl2 hfun => ?_⟩
  obtain ⟨hPd, hF⟩ := he2 z hz γ η κ hsup hrel hl1 hl2 hfun
  exact ⟨rlv_dnUp_latP Tf i hi v c _ _ γ' γ hl1' hl1,
    rlv_Q_of_dualP Tf i hi v c _ (γ'.1 * γ.1) (mul_mem γ'.2 γ.2) hPd, hF⟩

theorem rupLocM_of_rupLocW (Tf : FormsTied D u) (h : RUpLocW Tf) : RUpLocM Tf := rupLocM_of_V Tf (raising_local_v_of_local_w Tf h)

theorem rdnLocM_of_rdnLocW (Tf : FormsTied D u) (h : RDnLocW Tf) : RDnLocM Tf := rdnLocM_of_V Tf (lowering_local_v_of_local_w Tf h)

end TiedW

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

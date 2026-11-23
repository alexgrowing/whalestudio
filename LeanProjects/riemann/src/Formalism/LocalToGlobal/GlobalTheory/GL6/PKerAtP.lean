import Formalism.LocalToGlobal.UnitaryNorms.UnramT
import Formalism.LocalToGlobal.GlobalTheory.GL6.PDnDil
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocW
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrames

noncomputable section

open NumberField Ideal IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

section Unr

variable {D : D7} {u : D.what₂.Word}

theorem unramified_algebraic_weights (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧
      ∀ x ∈ A.Pv v, ∃ z : 𝓞 D.host.E, x * s = z * (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  have hres_nat : ∀ s : ℕ, A.res v (s : 𝓞 D.host.E) = 0 ↔ (D.mem u).A.T ∣ s := by
    intro s; rw [map_natCast]; exact CharP.cast_eq_zero_iff _ (D.mem u).A.T s
  have := Formalism.L2.Host.span_isPrime (D.mem u).A.T
  have hlies : (A.Pv v).LiesOver (span {((D.mem u).A.T : ℤ)}) := by
    refine ⟨?_⟩
    have hle : span {((D.mem u).A.T : ℤ)} ≤ (A.Pv v).comap (algebraMap ℤ (𝓞 D.host.E)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show A.res v (algebraMap ℤ (𝓞 D.host.E) ((D.mem u).A.T : ℤ)) = 0
      rw [map_natCast]
      exact (hres_nat _).2 dvd_rfl
    have hmax : (span {((D.mem u).A.T : ℤ)}).IsMaximal := by
      refine this.isMaximal ?_
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (D.mem u).A.T_prime.ne_zero
    exact hmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) hle
  obtain ⟨I, hI, hIP⟩ := Formalism.L2.Host.map_eq_mul_coprime D.host (D.mem u).A.T (Formalism.L2.Host.T_ne A v) (A.Pv v)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  refine ⟨s, hsP, fun x hx => ?_⟩
  have hxs : x * s ∈ (span {((D.mem u).A.T : ℤ)}).map (algebraMap ℤ (𝓞 D.host.E)) := by
    rw [hI]; exact Ideal.mul_mem_mul hx hsI
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at hxs
  obtain ⟨z, hz⟩ := hxs
  exact ⟨z, hz.symm⟩

theorem unr_smul (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∀ {W : Type} [AddCommGroup W] [Module (𝓞 D.host.E) W]
      (M : Submodule (𝓞 D.host.E) W), ∀ x ∈ A.Pv v • M,
        ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
  obtain ⟨s, hs, h⟩ := unramified_algebraic_weights A v
  refine ⟨s, hs, fun {W} _ _ M x hx => ?_⟩
  refine Submodule.smul_induction_on (p := fun x => ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) hx
    (fun p hp m hm => ?_) (fun x1 x2 h1 h2 => ?_)
  · obtain ⟨z, hz⟩ := h p hp
    exact ⟨z • m, M.smul_mem z hm, by rw [smul_smul, smul_smul, mul_comm s p, hz, mul_comm z]⟩
  · obtain ⟨a, ha, ea⟩ := h1
    obtain ⟨b, hb, eb⟩ := h2
    exact ⟨a + b, M.add_mem ha hb, by rw [smul_add, ea, eb, smul_add]⟩

theorem exists_smul_eq_smul_of_mem_ideal_smul {W : Type} [AddCommGroup W] [Module (𝓞 D.host.E) W] (A : AtTTied u) (v : (D.mem u).A.vT)
    (M : Submodule (𝓞 D.host.E) W) (x : W) (hx : x ∈ A.Pv v • M) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
  obtain ⟨s, hs, h⟩ := unr_smul A v
  obtain ⟨y, hy, e⟩ := h M x hx
  exact ⟨s, hs, y, hy, e⟩

theorem unr_sup_le {n : ℕ} (A : AtTTied u) (v : (D.mem u).A.vT) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z z' : Fin n → D.host.E) (hzz : ∃ t : 𝓞 D.host.E, t ∉ A.Pv v ∧ t • (z - z') ∈ A.Pv v • L) :
    Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (L ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) ≤
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (L ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z'}) := by
  obtain ⟨t, ht, htz⟩ := hzz
  obtain ⟨s, hs, y, hy, e⟩ := exists_smul_eq_smul_of_mem_ideal_smul A v L _ htz
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

  have key : (s * t) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z) =
      (s * t) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z') + y := by
    have e' : (s * t) • (z - z') = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by rw [mul_smul, e]
    have e2 : (s * t) • z = (s * t) • z' + (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
      rw [← e', smul_sub]; abel
    have e3 : (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) = y := by
      rw [show ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) = (((D.mem u).A.T : ℕ) : D.host.E) • y from
        (Nat.cast_smul_eq_nsmul (𝓞 D.host.E) _ y).trans (Nat.cast_smul_eq_nsmul D.host.E _ y).symm]
      rw [smul_smul, inv_mul_cancel₀ hT0, one_smul]
    rw [smul_comm (s * t) ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹) z, e2, smul_add, e3,
      smul_comm ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹) (s * t) z']
  intro x hx
  obtain ⟨r, hr, hrx⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨l, hl, w, hw, ex⟩ := Submodule.mem_sup.1 hrx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  refine (rlv_mem_locP _ _ _).2 ⟨s * t * r, ?_, ?_⟩
  · exact fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim
      (fun h' => (Ideal.IsPrime.mem_or_mem inferInstance h').elim hs ht) hr
  · rw [mul_smul, ← ex, smul_add, smul_comm (s * t) a, key, smul_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (L.smul_mem _ hl)) ?_
    refine Submodule.add_mem _ ?_ (Submodule.mem_sup_left (L.smul_mem _ hy))
    refine Submodule.mem_sup_right ?_
    rw [smul_comm a (s * t)]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

def TLdInt (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i), ∀ y ∈ Ld D u i hi c,
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y ∈ clsCrd D u i hi c

end Unr

section TLd

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

theorem tld_isLat (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Formalism.L2.GlobalTheoryTheory.Comp.IsLat (clsCrd D u i hi c) := by
  letI := D.host.cmStar
  set κ : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) with hκ
  have hform_eq : ∀ x y, (D.sp.X i).hT x y = Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (κ x) (κ y) := by
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
    unfold Formalism.UG.hform
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [gramN, hκ, CMData.sig, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, starRingEnd_apply]
  let K : Formalism.L2.GlobalTheoryTheory.Comp.Coord D.sp.cm (D.sp.X i) (Fin (D.R.N i)) := ⟨κ, gramN D i hi, hform_eq⟩
  exact K.isLat_lat (D.clsLat_lat u i c)

end TLd

section TLdLoc

open Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

end TLdLoc

section SFGen

open Matrix Formalism.UG IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sf_mulVec_smul {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (s : intV E v)
    (w : Fin n → E ⊗[F] v.adicCompletion F) : M *ᵥ (s • w) = s • (M *ᵥ w) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ * ((s : E ⊗[F] v.adicCompletion F) * w j) = (s : E ⊗[F] v.adicCompletion F) * (_ * w j)
  ring

set_option maxHeartbeats 1000000 in

theorem sf_of_gen {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L2 Lb : Submodule (𝓞 E) (Fin n → E))
    {Mm : Type} [AddCommGroup Mm] [Module (intV E v) Mm]
    (f : latS (F := F) (v.adicCompletion F) (intV E v) Lb →ₗ[intV E v] Mm)
    (y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔
      ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb))
    (hgen : ∀ z ∈ L2, ∀ h1 : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun i => inclE (F := F) (v.adicCompletion F) (z i)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb,
      f ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun i => inclE (F := F) (v.adicCompletion F) (z i))), (hg _).1 h1⟩ = f ⟨_, h1⟩) :
    g ∈ stabFun (latS (F := F) (v.adicCompletion F) (intV E v) Lb) f := by
  refine ⟨hg, fun x => ?_⟩
  have key : ∀ w (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2),
      f ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w),
        (hg _).1 ((hy2 w).1 hw)⟩ = f ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w, (hy2 w).1 hw⟩ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨z, hz, rfl⟩ := hw
      exact hgen z hz _
    | zero =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ 0),
          (hg _).1 ((hy2 0).1 (zero_mem _))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = 0 :=
        Subtype.ext (by simp)
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ 0, (hy2 0).1 (zero_mem _)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) = 0 :=
        Subtype.ext (by simp)
      rw [e1, e2]
    | add a b ha hb iha ihb =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (a + b)),
          (hg _).1 ((hy2 _).1 (add_mem ha hb))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a), (hg _).1 ((hy2 a).1 ha)⟩ +
          ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ b), (hg _).1 ((hy2 b).1 hb)⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add, Matrix.mulVec_add])
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (a + b), (hy2 _).1 (add_mem ha hb)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a, (hy2 a).1 ha⟩ +
          ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ b, (hy2 b).1 hb⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add, Matrix.mulVec_add])
      rw [e1, e2, map_add, map_add, iha, ihb]
    | smul s a ha iha =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (s • a)),
          (hg _).1 ((hy2 _).1 (Submodule.smul_mem _ s ha))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          s • ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a), (hg _).1 ((hy2 a).1 ha)⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; rw [sf_mulVec_smul, sf_mulVec_smul])
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (s • a), (hy2 _).1 (Submodule.smul_mem _ s ha)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          s • ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a, (hy2 a).1 ha⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; rw [sf_mulVec_smul])
      rw [e1, e2, map_smul, map_smul, iha]
  have e : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1) = x.1 := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hx : (y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 :=
    (hy2 _).2 (by rw [e]; exact x.2)
  have h := key _ hx
  have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
      ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1)), (hg _).1 ((hy2 _).1 hx)⟩ := Subtype.ext (by simp only [e])
  have e2 : x = ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1),
      (hy2 _).1 hx⟩ := Subtype.ext e.symm
  rw [e1, h, ← e2]

end SFGen

section SFGen2

open Matrix Formalism.UG IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sf_bc_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y1 y2 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (g : GL (Fin n) E) :
    ((bc (prV (E := E) v) (y1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g * y2) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) =
      (((bc (prV (E := E) v) y1)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
        ((g : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))) *
        ((bc (prV (E := E) v) y2 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  rfl

set_option maxHeartbeats 2000000 in

theorem sf_two {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L1 L2 Lb : Submodule (𝓞 E) (Fin n → E))
    {Mm : Type} [AddCommGroup Mm] [Module (intV E v) Mm]
    (f : latS (F := F) (v.adicCompletion F) (intV E v) Lb →ₗ[intV E v] Mm)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔
      ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔
      ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (Γ : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hgM : (g : Matrix (Fin n) (Fin n) _) = ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
      Γ.map (inclE (F := F) (v.adicCompletion F)) * (y2 : Matrix (Fin n) (Fin n) _))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb))
    (hF : ∀ z ∈ L2, ∃ a : 𝓞 F, a ∉ v.asIdeal ∧ (algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z) ∈ L1 ∧
      ∀ (h1 : ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z)) k)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb)
        (h2 : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • z) k)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb),
        f ⟨_, h1⟩ = f ⟨_, h2⟩) :
    g ∈ stabFun (latS (F := F) (v.adicCompletion F) (intV E v) Lb) f := by
  refine sf_of_gen v L2 Lb f y2 hy2 g hg ?_
  intro z hz h1
  have eG : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => inclE (F := F) (v.adicCompletion F) (z k))) =
      ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => inclE (F := F) (v.adicCompletion F) ((Γ *ᵥ z) k)) := by
    rw [hgM, mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      ← mulVec_mulVec]
    congr 1
    funext k
    exact (RingHom.map_mulVec _ _ _ k).symm
  obtain ⟨a, ha, hΓ, hfa⟩ := hF z hz
  let t : intV E v := ⟨(1 : E) ⊗ₜ[F] ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) :
      v.adicCompletion F), Subring.subset_closure (Or.inr ⟨⟨_, (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a).2⟩, rfl⟩)⟩
  have hι : ∀ y : Fin n → E, (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • y) k)) =
      t • (fun k => inclE (F := F) (v.adicCompletion F) (y k)) := by
    intro y; funext k
    show inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) a) • y k) =
      (t : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (y k)
    rw [rlv_incl_smul, mul_comm]; rfl
  have hA' : ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z)) k)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hy1 _).1 (Submodule.subset_span ⟨_, hΓ, rfl⟩)
  have hB' : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • z) k)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hy2 _).1 (Submodule.subset_span ⟨_, Submodule.smul_mem _ _ hz, rfl⟩)
  have hfT := hfa hA' hB'
  have eA : (⟨_, hA'⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = t • ⟨_, (hg _).1 h1⟩ := Subtype.ext (by
    simp only [Submodule.coe_smul]
    rw [hι, sf_mulVec_smul, eG])
  have eB : (⟨_, hB'⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = t • ⟨_, h1⟩ := Subtype.ext (by
    simp only [Submodule.coe_smul]
    rw [hι, sf_mulVec_smul])
  rw [eA, eB, map_smul, map_smul] at hfT
  obtain ⟨s, hs, hsr⟩ := rlv_unit (E := E) v a ha
  have hst1 : (⟨s, hs⟩ : intV E v) * t = 1 := Subtype.ext hsr
  have := congrArg (fun m => (⟨s, hs⟩ : intV E v) • m) hfT
  simp only [smul_smul, hst1, one_smul] at this
  exact this

end SFGen2

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end

import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfPt

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def DnMvL (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
    (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) ∧
  (∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (hx : γ.1.1 *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = g (T.lv0.prk v c ⟨_, hx⟩)) ∧
  ∀ (h : (D.mem u).C.Y 0 → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (T.val0.eY s') (T.val0.eY s) →
    (D.fm u).dnT 0 v c g h s = (((T.cls0.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

def UpMvL (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (z : ↥(Ld D u 0 (Nat.zero_le _) c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
    (T.cls0.y ((D.fm u).up 0 v c (T.lv0.pr v c z))).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
  (∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z))))
    (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
    (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩)) ∧
  ∀ (h : (D.mem u).C.Y 0 → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (T.val0.eY s') (T.val0.eY s) →
    (D.fm u).upT 0 v c (T.lv0.pr v c z) h s = (((T.cls0.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

def IsPtZ (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (y : (D.fm u).lk 0 v c) : Prop :=
  ∃ (s : 𝓞 D.host.E), s ∉ T.atT.Pv v ∧ ∃ (hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    T.lv0.prk v c ⟨_, hz⟩ = T.atT.res v s • y

def IsPt (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g)) (y : (D.fm u).lk 0 v c) : Prop :=
  ∃ z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)), T.lv0.pr v _ z = x ∧ IsPtZ T v c g γ z y

theorem dnMvL_ex (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (hg : g ≠ 0) :
    ∃ p : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ×
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      DnMvL T v c g p.1 p.2.1 p.2.2 := by
  obtain ⟨γ, η, κ, h⟩ := T.down_natural_level_zero v c g hg
  exact ⟨(γ, η, κ), h⟩

theorem upMvL_ex (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1) :
    ∃ p : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ×
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      UpMvL T v c z p.1 p.2.1 p.2.2 := by
  obtain ⟨γ, η, κ, h⟩ := T.up_natural_level_zero v c z hz
  exact ⟨(γ, η, κ), h⟩

set_option maxHeartbeats 4000000 in
theorem dnMvL_dnMvs (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {κ : T.cls0.lev.U} (h : DnMvL T v c g γ η κ) :
    (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
    ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T γ κ h := by
  obtain ⟨h1, h2, -, -, h5⟩ := h
  refine ⟨h1, h2, fun f => funext fun s => ?_⟩
  unfold natTr0
  rw [h5 f s _ ?_, Units.val_inv_eq_inv_val]
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ *
    (atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← mul_assoc]
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

set_option maxHeartbeats 4000000 in
theorem upMvL_isUp (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {z : ↥(Ld D u 0 (Nat.zero_le _) c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {κ : T.cls0.lev.U} (h : UpMvL T v c z γ η κ) : IsUpMvF T v c (T.lv0.pr v c z) η := by
  unfold IsUpMvF
  obtain ⟨h1, h2, -, -, -, h6⟩ := h
  refine ⟨γ, κ, h1, h2, ?_⟩
  intro f
  funext s
  unfold natTr0
  rw [h6 f s _ ?_, Units.val_inv_eq_inv_val]
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ *
    (atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← mul_assoc]
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

def IsPair (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (μ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (y : (D.fm u).lk 0 v c) : Prop :=
  g ≠ 0 ∧ ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), DnMvL T v c g γ η κ ∧
    ∃ (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
      (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ' : T.cls0.lev.U),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ z) = 1 ∧ UpMvL T v ((D.fm u).dn 0 v c g) z γ' μ κ' ∧
      IsPtZ T v c g γ z y

def PtEx (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ z, ∃ y, IsPtZ T v c g γ z y

def PtWd (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ x y y', IsPt T v c g γ x y → IsPt T v c g γ x y' → y = y'

def PtInj (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ x x' y, IsPt T v c g γ x y → IsPt T v c g γ x' y → x = x'

def PtSurj (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ y, ∃ x, IsPt T v c g γ x y

def ValSame (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∀ G ∈ AdFun T.cls0.lev (embT D),
    ∀ g η κ μ g' η' κ' μ' y, IsPair T v c g η κ μ y → IsPair T v c g' η' κ' μ' y →
      G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c * hcomp T η' κ' μ')

def ValTe (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∀ G ∈ AdFun T.cls0.lev (embT D),
    ∀ g η κ μ, IsPair T v c g η κ μ ((D.fm u).te 0 v c) → G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c)

def ValDia (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∃ τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ,
    ∀ G ∈ AdFun T.cls0.lev (embT D), ∀ (a : ((D.mem u).A.Fv v)ˣ) g η κ μ,
      IsPair T v c g η κ μ ((a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c) →
      ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
      ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ → G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c * δ)

set_option maxHeartbeats 8000000 in

theorem dUPt0F_of (T : Forms0 D u) (hE : PtEx T) (hW : PtWd T) (hI : PtInj T) (hS : PtSurj T)
    (vS : ValSame T) (vT : ValTe T) (vD : ValDia T) : DUPt0F T := by
  classical
  unfold DUPt0F
  intro v c
  obtain ⟨P, hP⟩ : ∃ P : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) × UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      ∀ g, g ≠ 0 → DnMvL T v c g (P g).1 (P g).2.1 (P g).2.2 :=
    ⟨fun g => if hg : g ≠ 0 then (dnMvL_ex T v c g hg).choose else 1,
      fun g hg => by simp only [dif_pos hg]; exact (dnMvL_ex T v c g hg).choose_spec⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)),
      ∀ g x, T.lv0.pr v _ (Z g x) = x.1 :=
    ⟨fun g x => (T.lv0.pr_surj v _ x.1).choose, fun g x => (T.lv0.pr_surj v _ x.1).choose_spec⟩
  have hZ1 : ∀ g x, (D.fm u).fv 0 v _ (T.lv0.pr v _ (Z g x)) = 1 := fun g x => by rw [hZ]; exact x.2
  obtain ⟨Q, hQ⟩ : ∃ Q : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) × UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      ∀ g x, UpMvL T v ((D.fm u).dn 0 v c g) (Z g x) (Q g x).1 (Q g x).2.1 (Q g x).2.2 :=
    ⟨fun g x => (upMvL_ex T v _ (Z g x) (hZ1 g x)).choose, fun g x => (upMvL_ex T v _ (Z g x) (hZ1 g x)).choose_spec⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), (D.fm u).lk 0 v c,
      ∀ g x, g ≠ 0 → IsPtZ T v c g (P g).1 (Z g x) (Y g x) :=
    ⟨fun g x => if hg : g ≠ 0 then (hE v c g hg _ _ _ (hP g hg) (Z g x)).choose else 0,
      fun g x hg => by simp only [dif_pos hg]; exact (hE v c g hg _ _ _ (hP g hg) (Z g x)).choose_spec⟩
  have key : ∀ g, g ≠ 0 → ∀ z y, IsPtZ T v c g (P g).1 z y → g y = (D.fm u).fv 0 v _ (T.lv0.pr v _ z) := by
    intro g hg z y hz0
    obtain ⟨s, hs, hz, hy⟩ := hz0
    obtain ⟨-, -, -, h4, -⟩ := hP g hg
    have hres : T.atT.res v s ≠ 0 := fun h0 => hs ((RingHom.mem_ker).2 h0)
    have hx : (P g).1.1.1 *ᵥ (s • z).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [Submodule.coe_smul, Matrix.mulVec_smul]; exact hz
    have h4' := h4 (s • z) hx
    have e : T.lv0.prk v c ⟨_, hx⟩ = T.lv0.prk v c ⟨_, hz⟩ := by
      congr 1; apply Subtype.ext; simp only [Submodule.coe_smul, Matrix.mulVec_smul]
    rw [e, hy, T.lv0.pr_smul] at h4'
    simp only [map_smul, smul_eq_mul] at h4'
    exact (mul_left_cancel₀ hres h4').symm
  have hpair : ∀ g (hg : g ≠ 0) x, IsPair T v c g (P g).2.1 (P g).2.2 (Q g x).2.1 (Y g x) :=
    fun g hg x => ⟨hg, (P g).1, hP g hg, Z g x, (Q g x).1, (Q g x).2.2, hZ1 g x, hQ g x, hY g x hg⟩
  refine ⟨fun g => (P g).1, fun g => (P g).2.1, fun g => (P g).2.2, fun g x => (Q g x).2.1, ?_, ?_, Y,
    (vD v c).choose, ?_, ?_, ?_⟩
  · intro g hg
    exact dnMvL_dnMvs T (hP g hg)
  · intro g x
    have h := upMvL_isUp T (hQ g x)
    rwa [hZ] at h
  · intro g hg x
    rw [key g hg _ _ (hY g x hg), hZ]
    exact x.2
  · intro g hg y hy
    obtain ⟨x', z', hz', hpz⟩ := hS v c g hg _ _ _ (hP g hg) y
    have hx1 : (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x' = 1 := by
      rw [← hz', ← key g hg z' y hpz, hy]
    refine ⟨⟨x', hx1⟩, ?_, ?_⟩
    · exact hW v c g hg _ _ _ (hP g hg) x' _ _ ⟨Z g ⟨x', hx1⟩, hZ g _, hY g _ hg⟩ ⟨z', hz', hpz⟩
    · intro x hx
      apply Subtype.ext
      refine hI v c g hg _ _ _ (hP g hg) x.1 x' y ⟨Z g x, hZ g x, ?_⟩ ⟨z', hz', hpz⟩
      rw [← hx]
      exact hY g x hg
  · intro G hG
    have hD : ∀ p : PD D u v c, (p.1 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) ≠ 0 := fun p h0 => by
      have h := p.1.2
      rw [h0, LinearMap.zero_apply] at h
      exact zero_ne_one h
    refine ⟨fun p hp => ?_, fun p q hpq => ?_, fun p q hpq => ?_, fun a q hq k hk δ hδ => ?_⟩
    · have h := hpair _ (hD p) p.2
      rw [hp] at h
      exact vT v c G hG _ _ _ _ h
    · have h1 := hpair _ (hD p) p.2
      have h2 := hpair _ q.1.2 q.2
      rw [← hpq] at h2
      exact vS v c G hG _ _ _ _ _ _ _ _ _ h1 h2
    · have h1 := hpair _ p.1.2 p.2
      have h2 := hpair _ q.1.2 q.2
      rw [← hpq] at h2
      exact vS v c G hG _ _ _ _ _ _ _ _ _ h1 h2
    · have h := hpair _ q.1.2 q.2
      rw [hq] at h
      exact (vD v c).choose_spec G hG a _ _ _ _ h k hk δ hδ

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end

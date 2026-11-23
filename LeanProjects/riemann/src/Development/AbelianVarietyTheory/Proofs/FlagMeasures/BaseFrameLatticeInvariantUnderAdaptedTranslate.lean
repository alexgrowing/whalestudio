import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgTr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Hom {T T' : E} (φ : S.V ≃ₗ[E] S.V) (A : LFlag S r T) (B : LFlag S r T') : Prop :=
  ∀ a : Fin (r + 1), φ (frame A a) - frame B a ∈ Xflag B a.val

theorem frame_castSucc {T : E} (A : LFlag S r T) (i : Fin r) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec, Fin.snoc_castSucc]

theorem frame_last {T : E} (A : LFlag S r T) : frame A (Fin.last r) = A.fl.z := by
  simp [frame, FlagG.fvec, Fin.snoc_last]

theorem xflag_mono {T : E} (A : LFlag S r T) {i j : ℕ} (h : i ≤ j) : Xflag A i ≤ Xflag A j := by
  exact Submodule.span_mono (Set.image_mono (fun k hk => lt_of_lt_of_le hk h))

theorem e_mem_xflag {T : E} (A : LFlag S r T) (i : Fin r) {j : ℕ} (h : i.1 < j) : A.fl.e i ∈ Xflag A j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem Hom.map_mem {T T' : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} (h : Hom φ A B)
    (j : ℕ) {x : S.V} (hx : x ∈ Xflag A j) : φ x ∈ Xflag B j := by
  have hle : Xflag A j ≤ (Xflag B j).comap (φ : S.V →ₗ[E] S.V) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    have h1 := h i.castSucc
    rw [frame_castSucc, frame_castSucc] at h1
    have h2 : φ (A.fl.e i) = (φ (A.fl.e i) - B.fl.e i) + B.fl.e i := by abel
    show φ (A.fl.e i) ∈ Xflag B j
    rw [h2]
    refine Submodule.add_mem _ ?_ (e_mem_xflag B i hi)
    exact xflag_mono B (le_of_lt hi) h1
  exact hle hx

theorem Hom.comp {T T' T'' : E} {φ ψ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} {C : LFlag S r T''}
    (hφ : Hom φ B C) (hψ : Hom ψ A B) : Hom (φ * ψ) A C := by
  intro a
  have e1 : (φ * ψ) (frame A a) - frame C a = φ (ψ (frame A a) - frame B a) + (φ (frame B a) - frame C a) := by
    rw [LinearEquiv.mul_apply, map_sub]; abel
  rw [e1]
  exact Submodule.add_mem _ (hφ.map_mem _ (hψ a)) (hφ a)

theorem Hom.inv {T : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} (h : Hom φ A A) : Hom φ⁻¹ A A := by
  have hW : ∀ j : ℕ, ∀ x ∈ Xflag A j, φ⁻¹ x ∈ Xflag A j := by
    intro j x hx
    set W := Xflag A j
    have : FiniteDimensional E W := FiniteDimensional.span_of_finite E ((Set.toFinite _).image _)
    have hle : W.map (φ : S.V →ₗ[E] S.V) ≤ W := by
      rintro y ⟨w, hw, rfl⟩
      exact h.map_mem j hw
    have heq : W.map (φ : S.V →ₗ[E] S.V) = W :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq φ W)
    rw [← heq] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have : φ⁻¹ (φ w) = w := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    simpa [this] using hw
  intro a
  have e1 : φ⁻¹ (frame A a) - frame A a = -(φ⁻¹ (φ (frame A a) - frame A a)) := by
    have : φ⁻¹ (φ (frame A a)) = frame A a := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    rw [map_sub, this]; abel
  rw [e1]
  exact Submodule.neg_mem _ (hW _ _ (h a))

theorem xflag_r {T : E} (A : LFlag S r T) : Xflag A r = Xsp A := by
  show Submodule.span E (A.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range A.fl.e)
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i; simp

theorem z_mem_orth {T : E} (A : LFlag S r T) : A.fl.z ∈ orth S (Xsp A) := by
  have hle : Xsp A ≤ LinearMap.ker (S.hT.flip A.fl.z) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    show S.hT.flip A.fl.z (A.fl.e i) = 0
    rw [LinearMap.flip_apply]; exact A.fl.z_orth i
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem Hom.of_nlam {T : E} {Λ : Submodule (𝓞 E) S.V} {n : S.V ≃ₗ[E] S.V} {A : LFlag S r T}
    (h : n ∈ NLam Λ A) : Hom n A A := by
  obtain ⟨-, h2, h3⟩ := h
  intro a
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_r]
    exact h3 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.val_castSucc]
    exact h2 i.1 _ (e_mem_xflag A i (Nat.lt_succ_self _))

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ A) a = γ (frame A a) := by
  induction a using Fin.lastCases with
  | last => simp [mapLF, hγ, frame_last, mapFlag]
  | cast i => simp [mapLF, hγ, frame_castSucc, mapFlag]

theorem Hom.of_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) :
    Hom γ A (mapLF γ A) := by
  intro a
  rw [frame_mapLF hγ, sub_self]
  exact Submodule.zero_mem _

theorem gmap_mul (φ ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (φ * ψ) Λ = Formalism.HermitianLatticesTheory.gmap φ (Formalism.HermitianLatticesTheory.gmap ψ Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_inv {φ : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap φ Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap φ⁻¹ Λ = Λ := by
  conv_lhs => rw [← h]
  rw [← gmap_mul, inv_mul_cancel]
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.Unfold.TgTr

namespace GlobalTheory.Unfold

open GlobalTheory.Unfold.TgTr in

theorem tg_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (t₀ s : TauC Y u u') (Λ₀ : LV D) (a a' n n' : GV D), TG F F' t₀ Λ₀ → a ∈ Aut0 (lf D (X.Fu u)) t₀.lam → a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam' → n ∈ NLam t₀.lam (lf D (X.Fu u)) → n' ∈ NLam t₀.lam' (lf D (X.Fu u')) → s.lam = t₀.lam → s.lin = n * (a * t₀.lin * a'⁻¹) * n' → TG F F' s Λ₀ := by
  intro D X Y u u' F F' t₀ s Λ₀ a a' n n' hTG ha ha' hn hn' hsl hsg
  obtain ⟨g, hgL, hgt, hΛ⟩ := hTG
  obtain ⟨⟨haI, haH⟩, haΛ⟩ := ha
  obtain ⟨⟨ha'I, ha'H⟩, -⟩ := ha'
  have hnH : Hom n _ _ := Hom.of_nlam hn
  have hn'H : Hom n' _ _ := Hom.of_nlam hn'
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1.1
  have hnΛ : Formalism.HermitianLatticesTheory.gmap n t₀.lam = t₀.lam := hn.1.2
  have ht₀I : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hsI : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  refine ⟨g * a⁻¹ * n⁻¹, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · exact Hom.comp (Hom.comp (φ := g) hgL.2 (Hom.inv haH)) (Hom.inv hnH)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · have hK : Hom (g * t₀.lin * a'⁻¹ * n') (lf D (X.Fu u')) F' :=
      Hom.comp (Hom.comp (Hom.comp (φ := g) hgt.2 (Hom.of_mapLF ht₀I _)) (Hom.inv ha'H)) hn'H
    have heq : g * a⁻¹ * n⁻¹ * s.lin = g * t₀.lin * a'⁻¹ * n' := by
      rw [hsg]; group
    intro c
    have hf : frame s.frame c = s.lin (frame (lf D (X.Fu u')) c) := frame_mapLF hsI _ c
    rw [hf, ← LinearEquiv.mul_apply, heq]
    exact hK c
  · rw [hsl, gmap_mul, gmap_mul, gmap_inv hnΛ, gmap_inv haΛ, hΛ]

end GlobalTheory.Unfold

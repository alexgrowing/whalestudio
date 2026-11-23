import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w'

section LES

theorem cls_congr {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {x y : K.X n} (h : x = y) (hx : K.d n x = 0)
    (hy : K.d n y = 0) : K.cls x hx = K.cls y hy := by
  subst h; rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}

theorem sq_mapH {K L : Cx.{w} R} {K' L' : Cx.{w'} R'} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L L' σ)
    (φ' : Cx.Hom K' L' (RingHom.id R')) (ψ' : Cx.Hom K K' σ)
    (h : ∀ n x, ψ.f n (φ.f n x) = φ'.f n (ψ'.f n x)) (n : ℕ) (z : K.H n) :
    ψ.mapH n (φ.mapH n z) = φ'.mapH n (ψ'.mapH n z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 z
  have c1 : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have c2 : L'.d n (ψ.f n (φ.f n x)) = 0 := by rw [ψ.comm, c1, map_zero]
  have c3 : K'.d n (ψ'.f n x) = 0 := by rw [ψ'.comm, hx, map_zero]
  have c4 : L'.d n (φ'.f n (ψ'.f n x)) = 0 := by rw [φ'.comm, c3, map_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx c1, CrystallineSemistableComparison.P.mapH_cls ψ n _ c1 c2, CrystallineSemistableComparison.P.mapH_cls ψ' n x hx c3,
    CrystallineSemistableComparison.P.mapH_cls φ' n _ c3 c4]
  exact cls_congr (h n x) _ _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_les [∀ i, Module.Flat R (N i)]
    {K L M : ι → Cx.{w} R} {K' L' M' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) (g : ∀ i, Cx.Hom (L i) (M i) (RingHom.id R))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (f' : Cx.Hom K' L' (RingHom.id R')) (g' : Cx.Hom L' M' (RingHom.id R'))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (a : ∀ i, N i → Cx.Hom (K i) K' σ) (b : ∀ i, N i → Cx.Hom (L i) L' σ) (c : ∀ i, N i → Cx.Hom (M i) M' σ)
    (hab : ∀ i n k x, (b i n).f k ((f i).f k x) = f'.f k ((a i n).f k x))
    (hbc : ∀ i n k x, (c i n).f k ((g i).f k x) = g'.f k ((b i n).f k x))
    (hL : ∀ j, Tens R (N := N) (M := fun i => (L i).H j) (M' := L'.H j) fun i n x => (b i n).mapH j x)
    (hM : ∀ j, Tens R (N := N) (M := fun i => (M i).H j) (M' := M'.H j) fun i n x => (c i n).mapH j x)
    (hadd : ∀ i j, ∃ F : N i ⊗[R] (K i).H j →+ K'.H j, ∀ n x, F (n ⊗ₜ x) = (a i n).mapH j x) :
    ∀ j, Tens R (N := N) (M := fun i => (K i).H j) (M' := K'.H j) fun i n x => (a i n).mapH j x := by
  intro j
  choose δ hδ h0 e1 e2 e3 using fun i => CrystallineSemistableComparison.P.les (f i) (g i) (hf i) (hfg i) (hg i)
  obtain ⟨δ', hδ', h0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  have dcomm : ∀ i n k z, (a i n).mapH (k + 1) (δ i k z) = δ' k ((c i n).mapH k z) := by
    intro i n k z
    obtain ⟨m, hm, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (M i) k).1 z
    obtain ⟨y, rfl⟩ := hg i k m
    obtain ⟨x, hx⟩ := CrystallineSemistableComparison.CechClassBoundaries.conn_ex (f i) (g i) (hfg i) y hm
    have hxc := CrystallineSemistableComparison.CechClassBoundaries.conn_cyc (f i) (hf i) y x hx
    have c3 : K'.d (k + 1) ((a i n).f (k + 1) x) = 0 := by rw [(a i n).comm, hxc, map_zero]
    have c4 : M'.d k ((c i n).f k ((g i).f k y)) = 0 := by rw [(c i n).comm, hm, map_zero]
    have c5 : M'.d k (g'.f k ((b i n).f k y)) = 0 := by rw [← hbc]; exact c4
    rw [hδ i k y x hm hxc hx, CrystallineSemistableComparison.P.mapH_cls (a i n) _ x hxc c3, CrystallineSemistableComparison.P.mapH_cls (c i n) k _ hm c4,
      cls_congr (hbc i n k y) c4 c5, hδ' k _ _ c5 c3 (by rw [← hab, hx, (b i n).comm])]
  cases j with
  | zero =>
    refine tens_five (M₁ := fun _ => PUnit.{w + 1}) (M₂ := fun _ => PUnit.{w + 1}) (L₁ := PUnit.{w' + 1}) (L₂ := PUnit.{w' + 1})
      (fun _ => 0) (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0)
      0 0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom
      (fun _ _ _ => 0) (fun _ _ _ => 0) _ (fun i n x => (b i n).mapH 0 x) (fun i n x => (c i n).mapH 0 x)
      (fun _ _ _ => rfl) (fun i n x => ?_) (fun i n x => ?_) (fun i n x => ?_)
      (fun i y => by simp) (fun i y => ?_) (fun i => e1 i 0)
      (fun y => by simp) (fun y => ?_) (e1' 0)
      (tens_zero (fun _ => inferInstance) inferInstance _) (tens_zero (fun _ => inferInstance) inferInstance _)
      (hL 0) (hM 0) (fun i => hadd i 0)
    · have : (0 : PUnit.{w + 1} →ₗ[R] (K i).H 0) x = 0 := rfl
      simp
    · exact sq_mapH (f i) (b i n) f' (a i n) (hab i n) 0 x
    · exact sq_mapH (g i) (c i n) g' (b i n) (hbc i n) 0 x
    · constructor
      · intro h
        have : y = 0 := h0 i (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
    · constructor
      · intro h
        have : y = 0 := h0' (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
  | succ k =>
    exact tens_five (fun i => (g i).mapH k) (fun i => δ i k) (fun i => (f i).mapH (k + 1)) (fun i => (g i).mapH (k + 1))
      (g'.mapH k).toAddMonoidHom (δ' k).toAddMonoidHom (f'.mapH (k + 1)).toAddMonoidHom (g'.mapH (k + 1)).toAddMonoidHom
      (fun i n x => (b i n).mapH k x) (fun i n x => (c i n).mapH k x) _
      (fun i n x => (b i n).mapH (k + 1) x) (fun i n x => (c i n).mapH (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) k x) (fun i n x => dcomm i n k x)
      (fun i n x => sq_mapH (f i) (b i n) f' (a i n) (hab i n) (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) (k + 1) x)
      (fun i => e2 i k) (fun i => e3 i k) (fun i => e1 i (k + 1)) (e2' k) (e3' k) (e1' (k + 1))
      (hL k) (hM k) (hL (k + 1)) (hM (k + 1)) (fun i => hadd i (k + 1))

end LES

end GlobalTheory.CompanionTheory.LocBC

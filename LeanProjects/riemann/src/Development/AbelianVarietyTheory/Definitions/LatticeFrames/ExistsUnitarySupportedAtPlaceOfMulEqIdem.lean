import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ReflectionBoostMatrixConjTransposeMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

structure Place (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] where

  e : AE D
  split : IsSplitIdem D e

  π : AE D →+* k

  ι : k →+ AE D
  π_ι : ∀ x, π (ι x) = x
  ι_π : ∀ a, ι (π a) = e * a
  cont_π : Continuous π
  cont_ι : Continuous ι

structure Frame (k : Type) [Field k] (N : ℕ) (Y : Type) [Fintype Y] [DecidableEq Y] where

  β : Matrix (Fin N) Y k

  γ : Matrix Y (Fin N) k
  βγ : β * γ = 1
  γβ : γ * β = 1

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

namespace Place

def pr (a : D.host.E) : k := p.π (incA D a)

def xi : k := p.pr D.host.xi0

def IsChar (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle) : Prop :=
  ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * p.ι x)

def IsComp (χ : (AE D)ˣ →* Circle) (μ : kˣ →* ℂˣ) : Prop :=
  ∀ (x : kˣ) (a : (AE D)ˣ), (a : AE D) = p.ι x + (1 - p.e) → (μ x : ℂ) = χ a

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def up {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) : WO S T :=
  (FT.β * x * FS.γ).map p.ι

def down {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (z : WO S T) : Matrix Y Y' k :=
  FT.γ * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β

def IsLoc {S : HSp D} (F : Frame k S.rank Y) (g : GA D S) (gk : GL Y k) : Prop :=
  SuppAt p.e S g ∧ (mt S g).map p.π = F.β * gk.val * F.γ

structure IsModel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) : Prop where

  theta : ∀ Φ, IsThetaFunO ψ S T (Tm Φ)

  trans : ∀ (x : Matrix Y Y' k) Φ Φ', (∀ t, Φ'.1 t = Φ.1 (t + x)) → Tm Φ' = heisO ψ S T (p.up FS FT x) (Tm Φ)

  modul : ∀ (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ Φ', (∀ t, Φ'.1 t = ψ (symplO S T (p.up FS FT t) y) * Φ.1 t) →
    Tm Φ' = heisO ψ S T y (Tm Φ)

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def hz {ρ : ℕ} (B : BesLev D ρ) : k := p.pr (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)

def IsCoreFrame {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) : Prop :=
  (∀ r a, F.β r (Sum.inl a) = (B.o.iA.map p.pr * FA.β) r a) ∧ ∀ r, F.β r (Sum.inr ()) = s * p.pr (vecB B.o B.ζ r)

def IsBesFrame {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ + 1 ∧ (∀ r a, F.β r (Sum.inl a) = ((B.d.i₀ * B.o.iA).map p.pr * FA.β) r a) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, F.β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i)) ∧
    (∀ j : Fin c, j.val = ρ → ∀ r, F.β r (Sum.inr j) = s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val = 2 * ρ → ∀ r,
      F.β r (Sum.inr j) = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i)

def IsJacFrame {ρ : ℕ} (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ ∧ (∀ r a, F.β r (Sum.inl a) = (J.d.i₀.map p.pr * F₀.β) r a) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, F.β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val + 1 = 2 * ρ → ∀ r,
      F.β r (Sum.inr j) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)

end Place

def Frame.ofGL {N : ℕ} (g : GL (Fin N) k) : Frame k N (Fin N) := ⟨g.val, (g⁻¹).val, by simp, by simp⟩

instance Frame.nonempty (N : ℕ) : Nonempty (Frame k N (Fin N)) := ⟨Frame.ofGL 1⟩

example : (Frame.ofGL (1 : GL (Fin 2) k)).β = 1 := rfl

def Place.ofSplitPt (q : GlobalTheory.FinPl.SplitPt D k) : Place D k :=
  ⟨q.e, q.split, q.pr, q.sec, q.pr_sec, q.sec_pr, q.cont_pr, q.cont_sec⟩

def Frame.ofFinPl {q : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    (F : GlobalTheory.FinPl.Frame q S n) : Frame k S.rank n := ⟨F.b, F.b', F.bb', F.b'b⟩

theorem Place.isChar_ofSplitPt (q : GlobalTheory.FinPl.SplitPt D k) {ψ : AddChar (AF D.host.F) ℂ} {χ ψk : AddChar k Circle}
    (hχ : q.IsChar ψ χ) : (Place.ofSplitPt q).IsChar ψ ψk ↔ ∀ x, ψk x = χ ((Place.ofSplitPt q).xi * x) := by
  have key : ∀ x, q.sec ((Place.ofSplitPt q).xi * x) = incA D D.host.xi0 * q.sec x := fun x => by
    change q.sec (q.pr (incA D D.host.xi0) * x) = _
    have h1 : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
    conv_lhs => rw [← q.pr_sec x, ← RingHom.map_mul, q.sec_pr, mul_left_comm, h1]
  refine forall_congr' fun x => ?_
  rw [Circle.ext_iff, hχ, key]
  rfl

theorem Place.down_ofSplitPt {q : GlobalTheory.FinPl.SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (α : GlobalTheory.FinPl.Frame q S n') (β : GlobalTheory.FinPl.Frame q T n) (t : WO S T) :
    (Place.ofSplitPt q).down (Frame.ofFinPl α) (Frame.ofFinPl β) t = GlobalTheory.FinPl.rd α β t := rfl

theorem Place.isLoc_ofSplitPt {q : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    (F : GlobalTheory.FinPl.Frame q S n) (g : GL n k) : (Place.ofSplitPt q).IsLoc (Frame.ofFinPl F) (F.gl g) g :=
  ⟨F.gl_supp g, F.gl_mat g⟩

example {n : Type} [Fintype n] [DecidableEq n] (B : BesLev D 1) (s : k) (FA : Frame k B.A.rank n)
    (F : Frame k B.V.rank (n ⊕ Fin 3)) (h : p.IsBesFrame B s FA F) (r) :
    F.β r (Sum.inr 0) = s * p.xi * p.pr (B.d.e r 0) ∧ F.β r (Sum.inr 1) = s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) ∧
      F.β r (Sum.inr 2) = -(s * (p.hz B / p.xi)) * p.pr (B.d.e' r 0) := by
  refine ⟨by simpa using h.2.2.1 0 0 rfl r, h.2.2.2.1 1 rfl r, ?_⟩
  rw [h.2.2.2.2 0 2 rfl r]
  simp [neg_div]

example {n : Type} [Fintype n] [DecidableEq n] (J : JacLev D 1) (s hh : k) (F₀ : Frame k J.W₀.rank n)
    (F : Frame k J.W.rank (n ⊕ Fin 2)) (h : p.IsJacFrame J s hh F₀ F) (r) :
    F.β r (Sum.inr 0) = s * p.xi * p.pr (J.d.e r 0) ∧ F.β r (Sum.inr 1) = s * (hh / p.xi) * p.pr (J.d.e' r 0) :=
  ⟨by simpa using h.2.2.1 0 0 rfl r, by simpa using h.2.2.2 0 1 rfl r⟩

namespace Witness
open GlobalTheory.SplitHalf
open scoped Topology

theorem exists_place {e : AE D} (he : IsSplitIdem D e) : ∃ v : HeightOneSpectrum (𝓞 D.host.F),
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    ∃ p : Place D (v.adicCompletion D.host.F), p.e = e := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  exact ⟨v, ⟨e, he, π, sec e v, chart_sec he.1 hπ, sec_chart he.1 hπ, chart_cont he hπ, sec_cont e v⟩, rfl⟩

theorem nonempty_place (D : D7) : ∃ v : HeightOneSpectrum (𝓞 D.host.F),
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    Nonempty (Place D (v.adicCompletion D.host.F)) := by
  obtain ⟨e, he⟩ := exists_idem D
  obtain ⟨v, p, -⟩ := exists_place he
  exact ⟨v, ⟨p⟩⟩

theorem e_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem exists_isChar {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) : ∃ ψk, p.IsChar ψ ψk :=
  ⟨{ toFun := fun x => ⟨psiE ψ (incA D D.host.xi0 * p.ι x), mem_sphere_zero_iff_norm.2 (hψ.1.2.1 _)⟩
     map_zero_eq_one' := Subtype.ext (by simp only [map_zero, mul_zero, psiE_zero]; rfl)
     map_add_eq_mul' := fun a b => Subtype.ext (by simp only [map_add, mul_add, psiE_add]; rfl) }, fun _ => rfl⟩

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
  (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)

theorem up_half (x) : IsHalf p.e (p.up FS FT x) := fun _ _ => e_ι p _

theorem up_add (x y) : p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add p.ι)]

theorem down_add (x y) : p.down FS FT (x + y) = p.down FS FT x + p.down FS FT y := by
  unfold Place.down
  rw [Matrix.map_add _ (map_add p.π), Matrix.mul_add, Matrix.add_mul]

theorem down_up (x) : p.down FS FT (p.up FS FT x) = x := by
  unfold Place.down Place.up
  have : ((FT.β * x * FS.γ).map p.ι).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  rw [this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem up_down {t : WO S T} (ht : IsHalf p.e t) : p.up FS FT (p.down FS FT t) = t := by
  unfold Place.down Place.up
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  ext i j
  exact (p.ι_π _).trans (ht i j)

theorem up_cont : Continuous (p.up FS FT) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι

theorem down_cont : Continuous (p.down FS FT) :=
  (continuous_const.matrix_mul (continuous_id.matrix_map p.cont_π)).matrix_mul continuous_const

def upH : Matrix Y Y' k →+ WO S T := AddMonoidHom.mk' (p.up FS FT) (up_add p FS FT)

def downH : WO S T →+ Matrix Y Y' k := AddMonoidHom.mk' (p.down FS FT) (down_add p FS FT)

theorem half_add {e : AE D} {x y : WO S T} (hy : IsHalf e y) : IsHalf e (x + y) ↔ IsHalf e x := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.add_apply, mul_add, hy i j, add_left_inj]

open Classical in

def ext : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ t := if IsHalf p.e t then Φ.1 (p.down FS FT t) else 0
  map_add' Φ Ψ := by funext t; simp only [Pi.add_apply, Submodule.coe_add]; split_ifs <;> simp
  map_smul' c Φ := by funext t; simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]; split_ifs <;> simp

open Classical in

theorem ext_apply (Φ) (t) : ext p FS FT Φ t = if IsHalf p.e t then Φ.1 (p.down FS FT t) else 0 := rfl

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
include hS hT

theorem lat_compact : IsCompact (((latO S T ΛS ΛT fun _ => True).comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
  convert (isCompact_half p.split hS hT).image (down_cont p FS FT) using 1
  ext x
  constructor
  · intro hx
    exact ⟨_, ⟨hx, up_half p FS FT x⟩, down_up p FS FT x⟩
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    change p.up FS FT (p.down FS FT t) ∈ (latO S T ΛS ΛT fun _ => True)
    rwa [up_down p FS FT h2]

theorem lat_open : IsOpen (((latO S T ΛS ΛT fun _ => True).comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
  convert (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 1 one_pos).preimage (up_cont p FS FT) using 1
  ext x
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    change (p.up FS FT x - 1 • p.up FS FT x).map _ = 0
    rw [one_smul, sub_self]
    exact Matrix.map_zero _ (finPart D).map_zero
  · rintro ⟨l, hl, h⟩
    have : p.up FS FT x = l := by
      ext i j
      have h1 := congrFun (congrFun h i) j
      rw [one_smul] at h1
      have h2 := congrFun (congrFun (GlobalTheory.SplitScalar.latO_fin hl) i) j
      have h3 := congrFun (congrFun (GlobalTheory.SplitScalar.half_fin p.split (up_half p FS FT x)) i) j
      refine GlobalTheory.SplitScalar.adele_ext (h3.trans h2.symm) (sub_eq_zero.1 ?_)
      rw [← RingHom.map_sub]
      exact h1
    change p.up FS FT x ∈ (latO S T ΛS ΛT fun _ => True)
    rwa [this]

theorem ext_sb (Φ) : IsSBHalf p.e (latO S T ΛS ΛT fun _ => True) (ext p FS FT Φ) := by
  classical
  obtain ⟨N, hN, h1⟩ := exists_inv Φ _ (lat_compact p FS FT hS hT)
  obtain ⟨M, hM, h2⟩ := exists_supp Φ.2.2 _ (lat_open p FS FT hS hT) fun x => by
    obtain ⟨n, hn, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 _
      (GlobalTheory.SplitScalar.half_fin p.split (up_half p FS FT x))
    exact ⟨n, hn, AddSubgroup.mem_comap.2 (by rw [map_nsmul]; exact h)⟩
  have hne : ∀ t, ext p FS FT Φ t ≠ 0 → IsHalf p.e t ∧ Φ.1 (p.down FS FT t) ≠ 0 := fun t ht => by
    rw [ext_apply] at ht
    split_ifs at ht with h
    · exact ⟨h, ht⟩
    · exact absurd rfl ht
  refine ⟨fun t ht => (hne t ht).1, N * M, Nat.mul_pos hN hM, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hh : IsHalf p.e ((N * M) • u) := fun i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu' i j]
    rw [ext_apply, ext_apply]
    refine if_congr (half_add hh) ?_ rfl
    have e1 : p.down FS FT ((N * M) • u) = N • (M • p.down FS FT u) := by
      rw [← mul_smul]; exact map_nsmul (downH p FS FT) _ _
    rw [down_add, e1]
    refine h1 _ (nsmul_mem ?_ _) _
    change p.up FS FT (p.down FS FT u) ∈ (latO S T ΛS ΛT fun _ => True)
    rwa [up_down p FS FT hu']
  · have h3 := AddSubgroup.mem_comap.1 (h2 _ (subset_tsupport _ (hne t ht).2))
    rw [map_nsmul] at h3
    change M • p.up FS FT (p.down FS FT t) ∈ _ at h3
    rw [up_down p FS FT (hne t ht).1] at h3
    rw [mul_smul]
    exact nsmul_mem h3 _

omit hS hT

theorem exists_isModel {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ Tm, p.IsModel ψ FS FT Tm ∧ Tm ≠ 0 := by
  classical
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) _ _ hS hT
  have hf1 := hf 1
  simp only [one_mul] at hf1
  have hO : GlobalTheory.PlaceModelSum.IsOrthSum p.e :=
    ⟨Unit, {()}, fun _ => p.e, fun _ _ => p.split, fun _ _ _ _ h => absurd rfl h, by simp⟩
  obtain ⟨T₀, h₀⟩ := hO.exists_model hψ hS hT p.split.2.1 hf1.2.1
  refine ⟨T₀.comp (ext p FS FT), ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩, fun h => f0 ?_⟩
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T _ _ hS hT p.e p.split.1 (GlobalTheory.PlaceCoord.infPart_split p.split)
      _ hf1.1 T₀ h₀ _ (ext_sb p FS FT hS hT Φ)
  · refine Eq.trans (congrArg T₀ ?_) (h₀.trans _ (ext_sb p FS FT hS hT Φ) _ (up_half p FS FT x))
    funext t
    rw [ext_apply, ext_apply, down_add, down_up, h]
    exact if_congr (half_add (up_half p FS FT x)).symm rfl rfl
  · refine Eq.trans (congrArg T₀ ?_) (h₀.modul _ (ext_sb p FS FT hS hT Φ) _ hy)
    funext t
    rw [ext_apply, ext_apply, h]
    split_ifs with ht
    · rw [up_down p FS FT ht]
    · rw [mul_zero]
  · have ho := lat_open p FS FT hS hT
    have hk := lat_compact p FS FT hS hT
    generalize hA : ((latO S T _ _ fun _ => True).comap (upH p FS FT) : AddSubgroup _) = A at ho hk
    have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
    let Φ : SB (Matrix Y Y' k) := ⟨(A : Set (Matrix Y Y' k)).indicator 1,
      (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩
    have e1 : ext p FS FT Φ = (1 : ℂ) • halfInd p.e (latO S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) fun _ => True) := by
      funext t
      rw [one_smul, ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht]
        change (A : Set (Matrix Y Y' k)).indicator 1 _ = _
        rw [Set.indicator_apply, ← hA]
        refine if_congr ?_ rfl rfl
        change p.up FS FT (p.down FS FT t) ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) fun _ => True) ↔ _
        rw [up_down p FS FT ht, and_iff_left ht]
      · rw [if_neg ht, if_neg fun h => ht h.2]
    have e2 : T₀ (ext p FS FT Φ) = 0 := congrArg (fun L => L Φ) h
    rw [e1, h₀.vac] at e2
    exact e2

theorem exists_isComp (χ : (AE D)ˣ →* Circle) : ∃ μ, p.IsComp χ μ := by
  have h1 := p.split.1
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  let j : k →* AE D :=
    { toFun := fun x => p.ι x + (1 - p.e)
      map_one' := by rw [ho, add_sub_cancel]
      map_mul' := fun x y => by
        rw [hm]
        linear_combination e_ι p x + e_ι p y - h1 }
  refine ⟨Circle.toUnits.comp (χ.comp (Units.map j)), fun x a h => ?_⟩
  have : Units.map j x = a := Units.ext h.symm
  simp only [MonoidHom.comp_apply, this]
  rfl

def mkFrame {N : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z] (β : Matrix (Fin N) Z k) (γ : Matrix Z (Fin N) k)
    (h : β * γ = 1) (hc : N = Fintype.card Z) : Frame k N Z :=
  ⟨β, γ, h, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hc])).1 h⟩

theorem card_frame {N : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z] (F : Frame k N Z) : N = Fintype.card Z := by
  simpa using Matrix.square_of_invertible (R := k) F.β F.γ F.βγ F.γβ

theorem exists_scaled {N : ℕ} {Z Z' : Type} [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (F : Frame k N Z)
    (σ : Z' ≃ Z) (t : Z' → k) (ht : ∀ z, t z ≠ 0) : ∃ F' : Frame k N Z', ∀ r z, F'.β r z = t z * F.β r (σ z) := by
  refine ⟨⟨Matrix.of fun r z => t z * F.β r (σ z), Matrix.of fun z r => (t z)⁻¹ * F.γ (σ z) r, ?_, ?_⟩, fun _ _ => rfl⟩
  · rw [← F.βγ]
    ext r s
    rw [Matrix.mul_apply, Matrix.mul_apply, ← σ.sum_comp]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Matrix.of_apply]
    field_simp [ht z]
  · ext z w
    have := congrFun (congrFun F.γβ (σ z)) (σ w)
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have e : ∀ r, (t z)⁻¹ * F.γ (σ z) r * (t w * F.β r (σ w)) = (t z)⁻¹ * t w * (F.γ (σ z) r * F.β r (σ w)) :=
      fun r => by ring
    simp only [e, ← Finset.mul_sum, this, Matrix.one_apply, σ.injective.eq_iff]
    split_ifs with h
    · rw [h, mul_one, inv_mul_cancel₀ (ht w)]
    · rw [mul_zero]

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem exists_witt {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (G₀ : Frame k V₀.rank Y) :
    ∃ F : Frame k V.rank (Y ⊕ (Fin σ ⊕ Fin σ)),
      F.β = fromCols (d.i₀.map p.pr * G₀.β) (fromCols (d.e.map p.pr) (d.e'.map p.pr)) := by
  have hs := congrArg (fun M => Matrix.map M (prH p)) d.sum_eq_one_rat
  simp only [Matrix.map_add _ (map_add (prH p)), Matrix.map_mul, Matrix.map_one _ (map_zero (prH p)) (map_one (prH p))] at hs
  refine ⟨mkFrame (fromCols (d.i₀.map p.pr * G₀.β) (fromCols (d.e.map p.pr) (d.e'.map p.pr))) (fromRows (G₀.γ * d.q0.map (prH p)) (fromRows (d.qX.map (prH p)) (d.qY.map (prH p)))) ?_ ?_, rfl⟩
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc G₀.β, G₀.βγ, Matrix.one_mul, ← hs]
    change (d.i₀.map (prH p) * _ + (d.e.map (prH p) * _ + d.e'.map (prH p) * _)) = _
    abel
  · simp [← card_frame G₀, ← d.rank_add]; ring

theorem exists_scaled' {N : ℕ} {Z Z' : Type} [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (F : Frame k N Z)
    (τ : Z → Z') (hτ : Function.Injective τ) (hc : Fintype.card Z = Fintype.card Z') (t : Z → k) (ht : ∀ z, t z ≠ 0) :
    ∃ F' : Frame k N Z', ∀ r z, F'.β r (τ z) = t z * F.β r z := by
  let σ := Equiv.ofBijective τ ((Fintype.bijective_iff_injective_and_card τ).2 ⟨hτ, hc⟩)
  obtain ⟨F', h⟩ := exists_scaled F σ.symm (fun z => t (σ.symm z)) fun z => ht _
  refine ⟨F', fun r z => ?_⟩
  have := h r (σ z)
  rwa [σ.symm_apply_apply] at this

theorem xi_ne : p.xi ≠ 0 := (map_ne_zero (prH p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne {ρ : ℕ} (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (prH p)).2 B.line.2

theorem exists_core {ρ : ℕ} (B : BesLev D ρ) {s : k} (hs : s ≠ 0) (FA : Frame k B.A.rank Y) :
    ∃ F, p.IsCoreFrame B s FA F := by
  have hL := B.line.1
  let ζ : Matrix (Fin B.L.rank) Unit D.host.E := Matrix.of fun r _ => B.ζ r
  let η : Matrix Unit (Fin B.L.rank) D.host.E :=
    Matrix.of fun _ r => (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)⁻¹ * (star B.ζ ᵥ* B.L.gram) r
  have h1 : η * ζ = 1 := by
    ext a b
    rw [Matrix.mul_apply, Subsingleton.elim a b, Matrix.one_apply_eq]
    simp only [η, ζ, Matrix.of_apply, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ i, (star B.ζ ᵥ* B.L.gram) i * B.ζ i = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ from (dotProduct_mulVec _ _ _).symm,
      inv_mul_cancel₀ B.line.2]
  have h2 : ζ * η = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hL])).1 h1
  have h3 : B.o.iA * B.o.qA + (B.o.iB * ζ) * (η * B.o.qB) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ζ, h2, Matrix.one_mul, B.o.iA_qA_add]
  have hs' := congrArg (fun M => Matrix.map M (prH p)) h3
  simp only [Matrix.map_add _ (map_add (prH p)), Matrix.map_one _ (map_zero (prH p)) (map_one (prH p))] at hs'
  rw [Matrix.map_mul, Matrix.map_mul] at hs'
  let F₀ : Frame k B.V₀.rank (Y ⊕ Unit) :=
    mkFrame (fromCols (B.o.iA.map (prH p) * FA.β) ((B.o.iB * ζ).map (prH p)))
      (fromRows (FA.γ * B.o.qA.map (prH p)) ((η * B.o.qB).map (prH p)))
      (by rw [fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc FA.β, FA.βγ, Matrix.one_mul, hs'])
      (by simp [← card_frame FA, ← B.o.rank_add, hL])
  obtain ⟨F, hF⟩ := exists_scaled' F₀ id Function.injective_id rfl (Sum.elim (fun _ => 1) fun _ => s)
    (by rintro (a | a) <;> simp [hs])
  exact ⟨F, fun r a => (hF r (Sum.inl a)).trans (one_mul _), fun r => hF r (Sum.inr ())⟩

theorem exists_jac {ρ : ℕ} (J : JacLev D ρ) {s hh : k} (hs : s ≠ 0) (hh0 : hh ≠ 0) (F₀ : Frame k J.W₀.rank Y) :
    ∃ F : Frame k J.W.rank (Y ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  obtain ⟨G, hG⟩ := exists_witt p J.d F₀
  have hx := xi_ne p
  obtain ⟨F, hF⟩ := exists_scaled' G
    (Sum.map id (Sum.elim (fun i : Fin ρ => (⟨i.val, by omega⟩ : Fin (2 * ρ))) fun i : Fin ρ => ⟨2 * ρ - 1 - i.val, by omega⟩))
    (by
      rintro (a | a | a) (b | b | b) h <;> simp [Fin.ext_iff] at h ⊢ <;> first | exact h | omega)
    (by simp; ring)
    (Sum.elim (fun _ => 1) (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val)))
    (by rintro (a | a | a) <;> simp [hs, hh0, hx])
  rw [hG] at hF
  refine ⟨F, rfl, fun r a => (hF r (Sum.inl a)).trans (one_mul _), fun i j h r => ?_, fun i j h r => ?_⟩
  · rw [show j = ⟨i.val, by omega⟩ from Fin.ext h]
    exact hF r (Sum.inr (Sum.inl i))
  · rw [show j = ⟨2 * ρ - 1 - i.val, by omega⟩ from Fin.ext (by simp only; omega)]
    exact hF r (Sum.inr (Sum.inr i))

theorem exists_bes {ρ : ℕ} (B : BesLev D ρ) {s : k} (hs : s ≠ 0) (FA : Frame k B.A.rank Y) :
    ∃ F : Frame k B.V.rank (Y ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F := by
  obtain ⟨F₀, h₀⟩ := exists_core p B one_ne_zero FA
  obtain ⟨G, hG⟩ := exists_witt p B.d F₀
  have hx := xi_ne p
  have hz := hz_ne p B
  obtain ⟨F, hF⟩ := exists_scaled' G
    (Sum.elim (Sum.map id fun _ => (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)))
      (Sum.elim (fun i : Fin ρ => Sum.inr (⟨i.val, by omega⟩ : Fin (2 * ρ + 1)))
        fun i : Fin ρ => Sum.inr ⟨2 * ρ - i.val, by omega⟩))
    (by
      rintro ((a | a) | a | a) ((b | b) | b | b) h <;> simp [Fin.ext_iff] at h ⊢ <;> first | exact h | omega)
    (by simp; ring)
    (Sum.elim (Sum.elim (fun _ => 1) fun _ => s)
      (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val)))
    (by rintro ((a | a) | a | a) <;> simp [hs, hz, hx])
  rw [hG] at hF
  refine ⟨F, rfl, fun r a => ((hF r (Sum.inl (Sum.inl a))).trans (one_mul _)).trans ?_, fun i j h r => ?_,
    fun j h r => ?_, fun i j h r => ?_⟩
  · change (B.d.i₀.map (prH p) * F₀.β) r (Sum.inl a) = ((B.d.i₀ * B.o.iA).map (prH p) * FA.β) r a
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun u _ => by rw [h₀.1]; rfl
  · rw [show j = ⟨i.val, by omega⟩ from Fin.ext h]
    exact hF r (Sum.inr (Sum.inl i))
  · rw [show j = ⟨ρ, by omega⟩ from Fin.ext h]
    refine (hF r (Sum.inl (Sum.inr ()))).trans (congrArg (s * ·) ?_)
    change (B.d.i₀.map (prH p) * F₀.β) r (Sum.inr ()) = prH p (∑ u, B.d.i₀ r u * vecB B.o B.ζ u)
    rw [Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [h₀.2, one_mul, map_mul]; rfl
  · rw [show j = ⟨2 * ρ - i.val, by omega⟩ from Fin.ext (by simp only; omega)]
    exact hF r (Sum.inr (Sum.inr i))

theorem exists_unitary_supportedAt_place_of_mul_eq_idem (a b : Mx D S.rank S.rank) (hba : b * a = p.e • (1 : Mx D S.rank S.rank)) :
    ∃ g : GA D S, SuppAt p.e S g ∧ (mt S g).map p.π = a.map p.π := by
  have h1 := p.split.1
  have h2 := p.split.2.1
  have h1' : cA D p.e * cA D p.e = cA D p.e := by rw [← RingHom.map_mul, h1]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  have p1 : p.π p.e = 1 := by rw [← ho, p.π_ι]
  have p2 : p.π (cA D p.e) = 0 := by rw [← one_mul (p.π _), ← p1, ← RingHom.map_mul, h2, RingHom.map_zero]
  refine ⟨ofMat S _ (reflectionBoost_matrix_conjTranspose_mul_self p.e _ _ a b h1 h2 rfl rfl hba), fun i j => ?_, ?_⟩
  · rw [mt_ofMat]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination a i j * (h1 + h2) + (giA S * (adj b * gA S)) i j * (h1' + h2) -
      (1 : Mx D S.rank S.rank) i j * (h1 + h1' + 2 * h2)
  · rw [mt_ofMat]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul,
      RingHom.map_sub, RingHom.map_one, p1, p2, one_mul, zero_mul, add_zero, sub_self]

theorem exists_isLoc (F : Frame k S.rank Y) (gk : GL Y k) : ∃ g, p.IsLoc F g gk := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  have mm : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) k, A * B = 1 →
      (A.map p.ι : Mx D S.rank S.rank) * B.map p.ι = p.e • (1 : Mx D S.rank S.rank) := fun A B h => by
    ext i j
    have := congrArg p.ι (congrFun (congrFun h i) j)
    rw [Matrix.mul_apply, map_sum] at this
    rw [Matrix.mul_apply, Matrix.smul_apply]
    simp only [Matrix.map_apply, ← hm]
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [ho, smul_eq_mul, mul_one]
    · rw [map_zero, smul_zero]
  have hAB : (F.β * (gk⁻¹).val * F.γ) * (F.β * gk.val * F.γ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc F.β gk.val, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gk⁻¹).val, Units.inv_mul, Matrix.one_mul, F.βγ]
  have hba := mm _ _ hAB
  have hπa : ((F.β * gk.val * F.γ).map p.ι).map p.π = F.β * gk.val * F.γ := Matrix.ext fun _ _ => p.π_ι _
  obtain ⟨g, g1, g2⟩ := exists_unitary_supportedAt_place_of_mul_eq_idem p _ _ hba
  exact ⟨g, g1, g2.trans hπa⟩

theorem hyp_flatBF {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J)
    {s : k} (hs : s ≠ 0) (FA : Frame k B.A.rank Y') (G₀ : Frame k J.W₀.rank Y) :
    ∃ (ψk : AddChar k Circle) (F₀ : Frame k B.V₀.rank (Y' ⊕ Unit)) (FV : Frame k B.V.rank (Y' ⊕ Fin (2 * ρ + 1)))
      (FW : Frame k J.W.rank (Y ⊕ Fin (2 * ρ))),
      p.IsChar ψ ψk ∧ p.IsCoreFrame B s FA F₀ ∧ p.IsBesFrame B s FA FV ∧ p.IsJacFrame J s (p.hz B) G₀ FW ∧
        ∃ Tm, p.IsModel ψ FV FW Tm ∧ Tm ≠ 0 := by
  obtain ⟨ψk, h0⟩ := exists_isChar p st.weil.std
  obtain ⟨F₀, h1⟩ := exists_core p B hs FA
  obtain ⟨FV, h2⟩ := exists_bes p B hs FA
  obtain ⟨FW, h3⟩ := exists_jac p J hs (hz_ne p B) G₀
  exact ⟨ψk, F₀, FV, FW, h0, h1, h2, h3, exists_isModel p FV FW st.weil.std⟩

theorem hyp_flatFB {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B)
    {s : k} (hs : s ≠ 0) (G₀ : Frame k J.W₀.rank Y') (FA : Frame k B.A.rank Y) :
    ∃ (ψk : AddChar k Circle) (FW : Frame k J.W.rank (Y' ⊕ Fin (2 * σ + 1 + 1))) (F₀ : Frame k B.V₀.rank (Y ⊕ Unit))
      (FV : Frame k B.V.rank (Y ⊕ Fin (2 * σ + 1))),
      p.IsChar ψ ψk ∧ p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW ∧ p.IsCoreFrame B (s * p.xi) FA F₀ ∧
        p.IsBesFrame B (s * p.xi) FA FV ∧ ∃ Tm, p.IsModel ψ FW FV Tm ∧ Tm ≠ 0 := by
  obtain ⟨ψk, h0⟩ := exists_isChar p st.weil.std
  have hx := xi_ne p
  obtain ⟨F₀, h1⟩ := exists_core p B (mul_ne_zero hs hx) FA
  obtain ⟨FV, h2⟩ := exists_bes p B (mul_ne_zero hs hx) FA
  obtain ⟨FW, h3⟩ := exists_jac p J hs (mul_ne_zero (neg_ne_zero.2 (pow_ne_zero 2 hx)) (hz_ne p B)) G₀
  exact ⟨ψk, FW, F₀, FV, h0, h3, h1, h2, exists_isModel p FW FV st.weil.std⟩

theorem hyp_contr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ)
    {s : k} (hs : s ≠ 0) {Z : Type} [Fintype Z] [DecidableEq Z] (FA : Frame k B.A.rank Y') (FA' : Frame k B'.A.rank Z)
    (F : Frame k S.rank Y) :
    ∃ (ψk : AddChar k Circle) (F₀ : Frame k B.V₀.rank (Y' ⊕ Unit)) (F₀' : Frame k B'.V₀.rank (Z ⊕ Unit)),
      p.IsChar ψ ψk ∧ p.IsCoreFrame B s FA F₀ ∧ p.IsCoreFrame B' (s * p.xi) FA' F₀' ∧
        (∃ T₁, p.IsModel ψ F₀ F T₁ ∧ T₁ ≠ 0) ∧ ∃ T₂, p.IsModel ψ F F₀' T₂ ∧ T₂ ≠ 0 := by
  obtain ⟨ψk, h0⟩ := exists_isChar p hψ
  obtain ⟨F₀, h1⟩ := exists_core p B hs FA
  obtain ⟨F₀', h2⟩ := exists_core p B' (mul_ne_zero hs (xi_ne p)) FA'
  exact ⟨ψk, F₀, F₀', h0, h1, h2, exists_isModel p F₀ F hψ, exists_isModel p F F₀' hψ⟩

theorem exists_haar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] : ∃ ν : Measure k, ν.IsAddHaarMeasure :=
  ⟨Measure.addHaar, inferInstance⟩

end Witness

def OmLoc (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω →
  ∀ (μS μT : kˣ →* ℂˣ), p.IsComp χS μS → p.IsComp χT μT →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm →
  ∀ g gk h hk, p.IsLoc FS g gk → p.IsLoc FT h hk → ∀ Φ Φ' : SB (Matrix Y Y' k),
    Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 → ω (g, h) (Tm Φ) = Tm Φ'

def FlatBF (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk →
  ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 →
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ)
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1)))
    (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)),
    p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW →
  ∀ Tm, p.IsModel ψ FV FW Tm → ∃ T₀, p.IsModel ψ F₀ G₀ T₀ ∧ ∀ Φ (Ψ : SB (Matrix n (n' ⊕ Unit) k)),
    Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = T₀ Ψ

def FlatFB (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk →
  ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 →
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ)
    (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1)))
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)),
    p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV →
  ∀ Tm, p.IsModel ψ FW FV Tm → ∃ T₀, p.IsModel ψ G₀ F₀ T₀ ∧ ∀ Φ (Ψ : SB (Matrix (n ⊕ Unit) n' k)),
    Ψ.1 = GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ.1 → flatFB st (Tm Φ) = T₀ Ψ

def Place.IsBiModel (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'')
    (Λ : SB (Matrix n n' k × Matrix n'' n k) →ₗ[ℂ] (WO A S → WO S A' → ℂ)) : Prop :=
  (∀ (Ξ₂ : SB (Matrix n'' n k)) (v : WO S A'), ∃ T₁, p.IsModel ψ FA FS T₁ ∧
    ∀ (Ξ₁ : SB (Matrix n n' k)) Ξ, (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → ∀ u, Λ Ξ u v = T₁ Ξ₁ u) ∧
  ∀ (Ξ₁ : SB (Matrix n n' k)) (u : WO A S), ∃ T₂, p.IsModel ψ FS FA' T₂ ∧
    ∀ (Ξ₂ : SB (Matrix n'' n k)) Ξ, (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → ∀ v, Λ Ξ u v = T₂ Ξ₂ v

theorem Witness.isModel_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y} {Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)}
    (h : p.IsModel ψ FS FT Tm) (c : ℂ) : p.IsModel ψ FS FT (c • Tm) := by
  have hs : ∀ y (f : WO S T → ℂ), c • heisO ψ S T y f = heisO ψ S T y (c • f) := fun y f => by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  · rw [LinearMap.smul_apply, ← map_smul]
    exact h.theta _
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, h.trans x Φ Φ' e, hs]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, h.modul y hy Φ Φ' e, hs]

theorem Witness.exists_prod {X X' U U' : Type} [TopologicalSpace X] [TopologicalSpace X'] (T₁ : SB X →ₗ[ℂ] (U → ℂ))
    (T₂ : SB X' →ₗ[ℂ] (U' → ℂ)) (n₁ : T₁ ≠ 0) (n₂ : T₂ ≠ 0) : ∃ Λ : SB (X × X') →ₗ[ℂ] (U → U' → ℂ), Λ ≠ 0 ∧
      ∀ (Ξ₁ : SB X) (Ξ₂ : SB X') Ξ, (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → ∀ u v, Λ Ξ u v = T₁ Ξ₁ u * T₂ Ξ₂ v := by
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB X X' (U → U' → ℂ)
    (LinearMap.mk₂ ℂ (fun Ξ₁ Ξ₂ u v => T₁ Ξ₁ u * T₂ Ξ₂ v)
      (fun _ _ _ => by funext u v; simp [add_mul]) (fun _ _ _ => by funext u v; simp [mul_assoc])
      (fun _ _ _ => by funext u v; simp [mul_add]) (fun _ _ _ => by funext u v; simp [mul_left_comm]))
  have key : ∀ (Ξ₁ : SB X) (Ξ₂ : SB X') Ξ, (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → ∀ u v, Λ Ξ u v = T₁ Ξ₁ u * T₂ Ξ₂ v :=
    fun Ξ₁ Ξ₂ Ξ e u v => by
      rw [show Ξ = GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂ from Subtype.ext (funext e), hΛ]
      rfl
  refine ⟨Λ, fun h => ?_, key⟩
  obtain ⟨Ξ₁, a₁⟩ := DFunLike.ne_iff.1 n₁
  obtain ⟨Ξ₂, a₂⟩ := DFunLike.ne_iff.1 n₂
  obtain ⟨u, hu⟩ := Function.ne_iff.1 a₁
  obtain ⟨v, hv⟩ := Function.ne_iff.1 a₂
  have := key Ξ₁ Ξ₂ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) (fun _ => rfl) u v
  rw [h] at this
  exact mul_ne_zero hu hv this.symm

theorem Witness.exists_isBiModel {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {n n' n'' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k A.rank n')
    (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') : ∃ Λ, p.IsBiModel ψ FA FS FA' Λ ∧ Λ ≠ 0 := by
  obtain ⟨T₁, h₁, n₁⟩ := Witness.exists_isModel p FA FS hψ
  obtain ⟨T₂, h₂, n₂⟩ := Witness.exists_isModel p FS FA' hψ
  obtain ⟨Λ, h0, key⟩ := Witness.exists_prod T₁ T₂ n₁ n₂
  refine ⟨Λ, ⟨fun Ξ₂ v => ⟨_, Witness.isModel_smul p h₁ (T₂ Ξ₂ v), fun Ξ₁ Ξ e u => ?_⟩,
    fun Ξ₁ u => ⟨_, Witness.isModel_smul p h₂ (T₁ Ξ₁ u), fun Ξ₂ Ξ e v => ?_⟩⟩, h0⟩
  · rw [key _ _ _ e, mul_comm, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  · rw [key _ _ _ e, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

def ContrLoc (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk →
  ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 →
  ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n)
    (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)),
    p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' →
  ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS F₀' T₂ →
    ∃ Λ : SB (Matrix n n' k × Matrix n'' n k) →ₗ[ℂ] (WO B.A S → WO S B'.A → ℂ), p.IsBiModel ψ FA FS FA' Λ ∧
      ∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix n n' k × Matrix n'' n k),
        Ξ.1 = GlobalTheory.LocFlat.contr ψk ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂) = Λ Ξ

def MixTLoc (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (S T T₀ : HSp D) (σ : ℕ) (d : HypDec T T₀ σ) (vT : VolM D σ S.rank)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FS : Frame k S.rank n') (G₀ : Frame k T₀.rank n)
    (FT : Frame k T.rank (n ⊕ (Fin σ ⊕ Fin σ))),
    FT.β = fromCols (d.i₀.map p.pr * G₀.β) (fromCols (d.e.map p.pr) (d.e'.map p.pr)) →
  ∀ Tm, p.IsModel ψ FS FT Tm → ∀ y : Mx D S.rank σ, ∃ T₀m, p.IsModel ψ FS G₀ T₀m ∧
    ∀ y' : Mx D S.rank σ, (∀ i j, (p.e + cA D p.e) * (y' - y) i j = (y' - y) i j) →
    ∀ Φ, ∃ Ψ : SB (Matrix n n' k), d.mixT S ψ vT.μ vT.𝓕 (Tm Φ) y' = T₀m Ψ ∧ ∀ x₀, Ψ.1 x₀ =
      ∫ ξ : Matrix (Fin σ) n' k, Φ.1 (fromRows x₀ (fromRows ξ (p.down FS FT (d.incAdj S y')).toRows₂.toRows₂)) *
        ψ (symplO S T (p.up FS FT (fromRows 0 (fromRows ξ 0))) (d.incAdj S y')) ∂(volM ν (Fin σ) n')

def MixSLoc (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (vS : VolM D T.rank ρ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (G₀ : Frame k S₀.rank n') (FT : Frame k T.rank n)
    (FS : Frame k S.rank (n' ⊕ (Fin ρ ⊕ Fin ρ))),
    FS.β = fromCols (d.i₀.map p.pr * G₀.β) (fromCols (d.e.map p.pr) (d.e'.map p.pr)) →
  ∀ Tm, p.IsModel ψ FS FT Tm → ∀ x : Mx D T.rank ρ, ∃ T₀m, p.IsModel ψ G₀ FT T₀m ∧
    ∀ x' : Mx D T.rank ρ, (∀ i j, (p.e + cA D p.e) * (x' - x) i j = (x' - x) i j) →
    ∀ Φ, ∃ Ψ : SB (Matrix n n' k), d.mixS T ψ vS.μ vS.𝓕 (Tm Φ) x' = T₀m Ψ ∧ ∀ x₀, Ψ.1 x₀ =
      ∫ b : Matrix n (Fin ρ) k, Φ.1 (fromCols x₀ (fromCols (p.down FS FT (d.extX T x')).toCols₂.toCols₁ b)) *
        ψ (symplO S T (p.up FS FT (fromCols 0 (fromCols 0 b))) (d.extX T x')) ∂(volM ν n (Fin ρ))

end GlobalTheory.LocMod
end

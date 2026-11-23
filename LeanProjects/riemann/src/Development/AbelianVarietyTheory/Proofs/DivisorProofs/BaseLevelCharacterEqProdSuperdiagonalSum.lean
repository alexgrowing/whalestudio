import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
noncomputable section

namespace GlobalTheory.TypeBase

def piCongrLeftMul {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) : (∀ a, P (e a)) ≃* ∀ b, P b :=
  { Equiv.piCongrLeft P e with
    map_mul' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.mul_apply, Equiv.piCongrLeft_apply_apply] }

theorem piCongrLeftMul_apply {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) (f : ∀ a, P (e a)) (a : α) :
    piCongrLeftMul P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

def bcEquiv {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A ≃+* B) :
    GL n A ≃* GL n B :=
  MonoidHom.toMulEquiv (Formalism.UG.bc (f : A →+* B)) (Formalism.UG.bc (f.symm : B →+* A))
    (by ext g i j; simp [Formalism.UG.bc]) (by ext g i j; simp [Formalism.UG.bc])

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A →+* B)
    (g : GL n A) (i j : n) : ((Formalism.UG.bc f g : GL n B) : Matrix n n B) i j = f ((g : Matrix n n A) i j) := rfl

theorem bc_mem_unip_iff {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A ≃+* B) (g : GL (Fin r) A) :
    Formalism.UG.bc (f : A →+* B) g ∈ unip B r ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.unitri r A := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := h1 (show j.val < i.val from hij)
      rw [bc_apply] at h
      exact f.injective (h.trans (map_zero f).symm)
    · have h := h2 i
      rw [bc_apply] at h
      exact f.injective (h.trans (map_one f).symm)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [bc_apply, h1 (show id j < id i from hij), map_zero]
    · rw [bc_apply, h2 i, map_one]

theorem edgeSum_bc {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A →+* B) (g : GL (Fin r) A) :
    edgeSum supEdge (Formalism.UG.bc f g) = f (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag (g : Matrix (Fin r) (Fin r) A)) := by
  simp only [edgeSum, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag, supEdge, bc_apply, map_sum, apply_ite f, map_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr

theorem det_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

theorem exists_char {Ks : Type} [Field Ks] (σ : Ks →+* ℂ) (p : ℕ) [Fact p.Prime] {ζ : Ks} (hζ : IsPrimitiveRoot ζ p)
    {k : Type} [CommRing k] (f : ZMod p ≃+* k) (χ : AddChar k ℂ) :
    ∃ ψ : AddChar (ZMod p) Ks, ∀ x, σ (ψ x) = χ (f x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz : χ (f 1) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero,
      AddChar.map_zero_eq_one]
  obtain ⟨k, -, hk⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz
  have hc : (ζ ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨AddChar.zmodChar p hc, fun x => ?_⟩
  rw [AddChar.zmodChar_apply, map_pow, map_pow, hk, ← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_zmod_val]

theorem baseLevelCharacter_eq_prod_superdiagonalSum {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) (g) (hg : g ∈ (P0 Pg r ψ).H) :
    (((P0 Pg r ψ).chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : Pg, ψ PP.1 (edgeSum supEdge (g PP)) := by
  unfold P0 LevelP.ofLocal
  dsimp only
  rw [MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

theorem mem_lastZeroOrthImageSubspace_iff {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (g : G0 Pg r) :
    g ∈ (P0 Pg r ψ).H ↔ ∀ PP, g PP ∈ unip (kP PP.1) r := by
  simp [P0, LevelP.ofLocal, Subgroup.mem_pi]

end GlobalTheory.TypeBase

namespace GlobalTheory.TypeBase

theorem base_level_unip_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.grp_chiW → (∀ k, ∃ ζ : Ks, IsPrimitiveRoot ζ (D.host.g k)) → ∀ (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), ∃ (t : LevelGroup D.host ≃* G) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Ks), (∀ u v, R.eG (t u) (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) ∧ (∀ v, ψ v ≠ 1) ∧ (∀ u, t u ∈ (F.lvl false).P ↔ u ∈ levelU D.host) ∧ ∀ u (h : t u ∈ (F.lvl false).P), algebraMap Ks D.what₂.LL (psiU ψ u) = ((F.lvl false).ψ ⟨t u, h⟩ : D.what₂.LLˣ) ∧ ∀ i, (R.FW i).chi (t u) = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hlevels hchiW hζ e iso
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let φ : LevelGroup D.host ≃* G0 R.Pg D.R.r :=
    (MulEquiv.piCongrRight fun v : Sq D.host => (bcEquiv (n := Fin D.R.r) (iso v))).trans
      (piCongrLeftMul (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e)
  have hφ : ∀ u v, φ u (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v) := fun u v =>
    piCongrLeftMul_apply (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e
      (fun v => Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) v
  have hex : ∀ v : Sq D.host, ∃ ψ : AddChar (ZMod (D.host.g v.1)) Ks,
      ∀ x, D.what₂.embLL (algebraMap Ks D.what₂.LL (ψ x)) = ψ0 (e v).1 (iso v x) := by
    intro v
    obtain ⟨ζ, hz⟩ := hζ v.1
    exact exists_char (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)) _ hz (iso v) (ψ0 (e v).1)
  choose ψ hψ using hex
  refine ⟨φ.trans R.eG.symm, ψ, fun u v => ?_, fun v h1 => ?_, fun u => ?_, fun u h => ?_⟩
  · show R.eG (R.eG.symm (φ u)) (e v) = _
    rw [MulEquiv.apply_symm_apply, hφ]
  · apply hgen (e v).1 (e v).2
    ext y
    obtain ⟨x, rfl⟩ := (iso v).surjective y
    rw [← hψ v x, h1, AddChar.one_apply, map_one, map_one, AddChar.one_apply]
  · show φ u ∈ (R.levR F false).H ↔ _
    rw [hlev, mem_lastZeroOrthImageSubspace_iff, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.levelU, Subgroup.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact (e.forall_congr fun v => by rw [hφ, bc_mem_unip_iff]).symm
  · have hm : φ u ∈ (P0 R.Pg D.R.r ψ0).H := by rw [← hlev]; exact h
    have hun : ∀ PP, φ u PP ∈ unip (kP PP.1) D.R.r := (mem_lastZeroOrthImageSubspace_iff _ _ _ _).1 hm
    refine ⟨?_, fun i => ?_⟩
    · apply D.what₂.embLL.injective
      have e1 : (R.levR F false).chi ⟨φ u, h⟩ =
          Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩) := rfl
      have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
          ((X.chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (g PP)) := by
        rintro X rfl g hg
        exact baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ g hg
      have h2 := key _ hlev (φ u) h
      rw [e1, Units.coe_map] at h2
      rw [show D.what₂.embLL (((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (φ u PP)) from h2]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.psiU, map_prod]
      refine Finset.prod_equiv e (by simp) fun v _ => ?_
      rw [hψ, hφ, edgeSum_bc, RingEquiv.coe_toRingHom]
    · apply Units.ext
      apply D.what₂.embLL.injective
      have hg : R.eG ((φ.trans R.eG.symm) u) = φ u := R.eG.apply_symm_apply _
      rw [hchiW i, hg, Finset.prod_eq_one (fun PP _ => by rw [det_unip (hun PP), map_one, Units.val_one]),
        Units.val_one, map_one]

end GlobalTheory.TypeBase

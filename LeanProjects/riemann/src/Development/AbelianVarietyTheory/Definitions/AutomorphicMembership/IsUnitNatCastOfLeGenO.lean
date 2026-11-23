import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtOmPHtEval
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlgOfFlagClSpec

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.isUnit_natCast_of_le_genO (B : Mdl Y i₀) {V : B.X.Opens} (hV : V ≤ B.genO) : IsUnit ((p : ℕ) : Γ(B.X, V)) := by
  have := (B.X.toRingedSpace.isUnit_res_basicOpen ((p : ℕ) : Γ(B.X, ⊤))).map (B.X.presheaf.map (homOfLE hV).op).hom
  exact (map_natCast ((B.X.presheaf.map (homOfLE hV).op).hom.comp
    (B.X.presheaf.map (homOfLE (B.X.basicOpen_le _)).op).hom) p) ▸ this

theorem HTm.omP_sec_eq_top {Z : Mdl Y i₀} {n : ℕ} (h : HTm.HTOn Z n) {V : Z.X.Opens} (hV : V ≤ Z.genO) :
    (HTm.omP h).sec V = ⊤ := eq_top_iff.2 fun s _ => by
  obtain ⟨u, hu⟩ := (Z.isUnit_natCast_of_le_genO hV).pow n
  have := HTm.pow_smul_mem_omP h ((↑u⁻¹ : Γ(Z.X, V)) • s)
  rwa [← Nat.cast_smul_eq_nsmul Γ(Z.X, V), Nat.cast_pow, ← hu, smul_smul, Units.mul_inv, one_smul] at this

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop} {Z Z' : Mdl Y i₀}

theorem Step.admitted.of_isMap {t : Step Y i₀} (h : t.admitted P Z) {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) : t.admitted P Z' := by
  refine ⟨.inr ?_, h.2⟩
  obtain rfl | ⟨g, hg⟩ := h.1
  exacts [⟨f, hf⟩, ⟨f ≫ g, MapComp.isMap_comp hf hg⟩]

namespace FlagFam

def single (t : Step Y i₀) (h : t.admitted P Z) : FlagFam P Z := ⟨{t}, fun _ ht => Finset.mem_singleton.1 ht ▸ h⟩

open Classical in

def union (s s' : FlagFam P Z) : FlagFam P Z := ⟨s.1 ∪ s'.1, fun t ht => (Finset.mem_union.1 ht).elim (s.2 t) (s'.2 t)⟩

theorem mem_union {s s' : FlagFam P Z} {t : Step Y i₀} : t ∈ (s.union s').1 ↔ t ∈ s.1 ∨ t ∈ s'.1 := by
  classical
  exact Finset.mem_union

def pull (s : FlagFam P Z) {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) : FlagFam P Z' := ⟨s.1, fun t ht => (s.2 t ht).of_isMap hf⟩

end FlagFam

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

def flgTrue : FlgSt ct := flgOf ct (IsHTLatOf (htmTrue ct))

theorem isFlagCl_flgTrue (Z : ct.Mdl) (s : (flgTrue ct).FlagData Z) : IsFlagCl Z s.1 ((flgTrue ct).flagCl Z s) :=
  flgOf_flagCl_spec D A N j S κ p ct _ Z s

namespace HTm

variable {ct} {Z : ct.Mdl}

theorem isHTLatOf_iff {L : Lat Z} : IsHTLatOf (htmTrue ct) Z L ↔
    (∃ n, IsHTBlowup ct Z (ct.Xn n)) ∧ ∀ y : ct.Pt Z, latAt ct y (omSub ct Z) = latAt ct y L.N :=
  and_congr_left' (exists_congr fun _ => and_iff_right_of_imp fun H => ((isHTBlowup_iff ct).1 H).choose_spec.1)

variable (ct Z) in

def OmFree : Prop := ∀ x : Z.X, ∃ (V : Z.X.Opens) (r : ℕ) (m : Fin r → Γ((omSub ct Z).toMod, V)), x ∈ V ∧ VB.IsFrame m

def omLat (hf : OmFree ct Z) : Lat Z where
  N := omSub ct Z
  free := hf
  gen _ hV := omP_sec_eq_top _ hV

def htStep {B : ct.Mdl} {L : Lat B} (hL : IsHTLatOf (htmTrue ct) B L) {f : Z.X ⟶ B.X} (hf : IsMap Z B f)
    (σ : D.host.E →+* ℂ) (k : ℕ) (hk : k ≤ S.Dw.mult σ) : (flgTrue ct).FlagData Z :=
  FlagFam.single ⟨B, L, σ, k, hk⟩ ⟨.inr ⟨f, hf⟩, .inr hL⟩

variable (ct Z) in

def htFam : (flgTrue ct).FlagData Z := classFam (IsHTLatOf (htmTrue ct)) Z

end HTm

example : (flgTrue ct).flagCl ct.Xm (flgTrue ct).allFlags = ct.YY := (flgTrue ct).YY_eq.symm

example (Z : ct.Mdl) : (flgTrue ct).flagCl Z (FlagFam.empty Z) = Z := ct.flagCl_empty Z

example (σ : D.host.E →+* ℂ) (k : ℕ) (hk : k ≤ S.Dw.mult σ) :
    ((flgTrue ct).flagCl ct.Xm (FlagFam.single ⟨ct.Xm, Lat.top _, σ, k, hk⟩ ⟨.inl rfl, .inl Lat.isTop_top⟩)).ty σ = {k} := by
  refine ((isFlagCl_flgTrue ct _ _).2.1 σ).trans ?_
  rw [show ct.Xm.ty σ = ∅ from ct.B.ty none σ]
  ext r
  simp [mem_stepTy, FlagFam.single, eq_comm]

example (Z : ct.Mdl) (h : ¬ ∃ n, HTm.IsHTBlowup ct Z (ct.Xn n)) : ∃ hf : HTm.OmFree ct Z, HTm.omLat hf = Lat.top Z := by
  have e : HTm.htData ct Z = ⟨0, 0⟩ := dif_neg fun ⟨d, hd⟩ => h ⟨d.1, (HTm.isHTBlowup_iff ct).2 ⟨d.2, hd⟩⟩
  have k : ∀ V, (HTm.omSub ct Z).sec V = (Lat.top Z).N.sec V := fun V => by
    rw [Lat.isTop_top V, HTm.omSub, e, eq_top_iff]
    exact fun s _ => by simpa using HTm.pow_smul_mem_omP (0 : HTm.HTOn Z 0) s
  have k' : HTm.omSub ct Z = (Lat.top Z).N := by
    generalize HTm.omSub ct Z = M, (Lat.top Z).N = M' at k
    cases M; cases M'; obtain rfl := funext k; rfl
  exact ⟨by rw [HTm.OmFree, k']; exact (Lat.top Z).free, Lat.ext k⟩

example (Z : ct.Mdl) (h : ¬ ∃ n, HTm.IsHTBlowup ct Z (ct.Xn n)) (L : Lat Z) : ¬ IsHTLatOf (htmTrue ct) Z L :=
  fun hL => h (HTm.isHTLatOf_iff.1 hL).1

end GlobalTheory.LocM

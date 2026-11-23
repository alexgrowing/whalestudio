import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationally
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.CrystallineBase

variable {l : ℕ} [Fact l.Prime]

def resLt {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL) : Lt K' LL where
  V := T.V
  acg := T.acg
  modLL := T.modLL
  modQp := T.modQp
  towQp := T.towQp
  modO := T.modO
  towO := T.towO
  top := T.top
  cadd := T.cadd
  csmul := T.csmul
  mtop := T.mtop
  fdim := T.fdim
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont := fun x => (T.cont x).comp (continuous_subtype_val.subtype_mk _)
  L := { T := T.L.T
         stable := fun g x hx => T.L.stable _ x hx
         fg := T.L.fg
         free := T.L.free
         span := T.L.span }

theorem gks_eq (P : LocPrime l) (H : LocHW l P) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) :
    (H.W K s LL h).GKs = ((Ks K s).fixingSubgroup).subgroupOf (GK K) := by
  ext x
  rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, H.W_s, Subgroup.mem_subgroupOf]
  rfl

theorem base_setup (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : ∃ (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K ∧
      ((HW l).W K' s LL h').GKs = ⊤ ∧
      ∀ g : ↥(GK K), g ∈ ((HW l).W K s LL h).GKs ↔ (g : GQ l) ∈ GK K' := by
  haveI hfin : FiniteDimensional ℚ_[l] ↥(Ks K s) := GlobalTheory.InvariantLift.finKs K s
  obtain ⟨K', hK'⟩ : ∃ K' : FinExt l, K'.1 = Ks K s := ⟨⟨_, hfin⟩, rfl⟩
  have hle : K.1 ≤ K'.1 := hK' ▸ h.2.2.1
  have h0le : K0 K ≤ K0 K' := inf_le_inf_right _ hle
  have hK0 : K0 K' = K0 K := by
    have hr := GlobalTheory.Cyc.finrank_maxUnramified_eq_cyclotomicLevel K K' s h.1 hK' hle
    exact (IntermediateField.eq_of_le_of_finrank_eq h0le hr.symm).symm
  have hKs : Ks K' s = K'.1 := by
    apply le_antisymm
    · rw [hK']; exact sup_le (hK' ▸ inf_le_left) le_sup_right
    · rw [hK']; exact sup_le_sup_right h0le _
  have h' : Good K' s LL := by
    refine ⟨h.1, h.2.1, hKs.ge, fun τ x => ?_⟩
    have hKs' : Ks K' s = Ks K s := hKs.trans hK'
    exact h.2.2.2 (τ.comp (IntermediateField.equivOfEq hKs'.symm).toAlgHom) ⟨x.1, hKs' ▸ x.2⟩
  refine ⟨K', h', hle, hK0, ?_, fun g => ?_⟩
  · rw [gks_eq (D.loc l) (HW l) K' s LL h', hKs]
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_top, iff_true]
    exact g.2
  · rw [gks_eq (D.loc l) (HW l) K s LL h, Subgroup.mem_subgroupOf]
    show _ ↔ (g : GQ l) ∈ K'.1.fixingSubgroup
    rw [hK']

theorem restrict_crys (D : Formalism.BasicNotions.D7) {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL)
    (hT : IsCrys ((D.loc l).PD K) T.ρ) : IsCrys ((D.loc l).PD K') (resLt (K := K) (K' := K') (LL := LL) hle T).ρ :=
  (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) (D.locT l) K K' LL hle T.V T.ρ).1 hT

theorem restrict_jumps (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1) (T : Lt K LL)
    (hT : IsCrys ((D.loc l).PD K) T.ρ) (M hh : Let K → ℕ) (hJ : JumpsLet ((HW l).W K s LL h) T M hh)
    (Ljumps : ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      IsJumpV ((D.loc l).PD K') (T.ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a →
        IsJumpV ((D.loc l).PD K) T.ρ (τ'.comp (IntermediateField.inclusion hle)) a) :
    JumpsLet ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (fun _ => mx M) (fun _ => mx hh) := by
  have hnpos : 0 < Module.finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨hnpos.ne'⟩
  intro τ' i' _ a ha
  have ha2 := Ljumps τ' a ha
  obtain ⟨i, hi⟩ := ((HW l).W K s LL h).emb_bij.2
    ((τ'.comp (IntermediateField.inclusion hle)).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  have hm := hJ (τ'.comp (IntermediateField.inclusion hle)) i hi.symm a ha2
  have hb1 : M i ≤ mx M := le_ciSup (Set.finite_range M).bddAbove i
  have hb2 : hh i ≤ mx hh := le_ciSup (Set.finite_range hh).bddAbove i
  simp only [Set.mem_Icc] at hm ⊢
  constructor <;> omega

def eMap {K K' : FinExt l} (hle : K.1 ≤ K'.1) (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ H) : ↥H' → ↥H :=
  fun g => ⟨⟨((g : ↥(GK K')) : GQ l), GK_le hle (g : ↥(GK K')).2⟩, hm _⟩

theorem eMap_cont {K K' : FinExt l} (hle : K.1 ≤ K'.1) (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ H) : Continuous (eMap hle H H' hm) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem pull_cocycle {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL) (H : Subgroup ↥(GK K))
    (H' : Subgroup ↥(GK K')) (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ H)
    (c : ↥(latticeCocycles (resLat T H))) : ∃ c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H')),
      ∀ g, (c' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) g = (c : ↥H → T.V) (eMap hle H H' hm g) :=
  ⟨⟨fun g => (c : ↥H → T.V) (eMap hle H H' hm g),
    ⟨⟨c.2.1.1.comp (eMap_cont hle H H' hm), fun g g' => c.2.1.2 (eMap hle H H' hm g) (eMap hle H H' hm g')⟩, fun g _ => c.2.2 _ trivial⟩⟩,
    fun _ => rfl⟩

theorem pull_f (P : LocPrime l) {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL)
    (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ H)
    (c : ↥H → T.V) (c' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (hc : ∀ g, c' g = c (eMap hle H H' hm g))
    (x : T.V ⊗[ℚ_[l]] P.R.B) (hx : ∀ g : ↥H, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T.ρ g x - x) :
    ∀ g : ↥H', c' g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K') (resLt (K := K) (K' := K') (LL := LL) hle T).ρ g (@id ((resLt (K := K) (K' := K') (LL := LL) hle T).V ⊗[ℚ_[l]] P.R.B) x) - @id ((resLt (K := K) (K' := K') (LL := LL) hle T).V ⊗[ℚ_[l]] P.R.B) x := by
  intro g
  rw [hc]
  exact (hx (eMap hle H H' hm g)).trans (congrArg
    (fun f : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B => f x - x)
    (GlobalTheory.Cyc.actVB_inclusion P K K' LL hle T (g : ↥(GK K'))).symm)

end GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineBase

variable {l : ℕ} [Fact l.Prime]

def fMap {K K' : FinExt l} (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥H, ((g : ↥(GK K)) : GQ l) ∈ GK K') (htop : H' = ⊤) : ↥H → ↥H' :=
  fun g => ⟨⟨((g : ↥(GK K)) : GQ l), hm g⟩, by rw [htop]; trivial⟩

theorem fMap_cont {K K' : FinExt l} (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥H, ((g : ↥(GK K)) : GQ l) ∈ GK K') (htop : H' = ⊤) : Continuous (fMap H H' hm htop) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem resΓ_one_iff (P : LocPrime l) (K LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (g : ↥(GK K)) :
    W.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have hres := W.χΓ_res g
  rw [P.PD_χ] at hres
  constructor
  · intro h1
    rw [h1, map_one, Units.val_one, map_one, eq_comm] at hres
    have : (P.χQ (g : GQ l) : ℚ_[l]) = 1 :=
      (algebraMap ℚ_[l] ↥LL.1).injective (by rw [hres, map_one])
    exact Units.ext this
  · intro h1
    rw [h1, Units.val_one, map_one] at hres
    have h2 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 :=
      Subtype.val_injective (by change algebraMap ↥(OL LL) ↥LL.1 _ = algebraMap ↥(OL LL) ↥LL.1 1; rw [hres, map_one])
    exact W.χΓ_inj (by rw [map_one]; exact Units.ext h2)

set_option maxHeartbeats 2000000 in

theorem push_class {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL) (H : Subgroup ↥(GK K))
    (H' : Subgroup ↥(GK K')) (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ H)
    (hm' : ∀ g : ↥H, ((g : ↥(GK K)) : GQ l) ∈ GK K') (htop : H' = ⊤)
    (cW cκ : ↥(latticeCocycles (resLat T H))) (c'' cκ' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H')))
    (hW : ∀ g, (cW : ↥H → T.V) g = (c'' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap H H' hm' htop g))
    (hκ : ∀ g, (cκ' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) g = (cκ : ↥H → T.V) (eMap hle H H' hm g))
    (n : ℕ) (h : (Submodule.Quotient.mk c'' : LatticeCohomology (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H')) =
      n • Submodule.Quotient.mk cκ') :
    (Submodule.Quotient.mk cW : LatticeCohomology (resLat T H)) = n • Submodule.Quotient.mk cκ := by
  have e1 : (n • Submodule.Quotient.mk cκ' : LatticeCohomology (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H')) = Submodule.Quotient.mk (n • cκ') :=
    (map_nsmul (Submodule.mkQ _) n cκ').symm
  have e2 : (n • Submodule.Quotient.mk cκ : LatticeCohomology (resLat T H)) = Submodule.Quotient.mk (n • cκ) :=
    (map_nsmul (Submodule.mkQ _) n cκ).symm
  rw [e1] at h
  rw [e2]
  have h3 := (Submodule.Quotient.eq _).1 h
  apply (Submodule.Quotient.eq _).2
  rw [Submodule.mem_comap] at h3 ⊢
  obtain ⟨t, ht, hteq⟩ := h3
  refine ⟨t, ht, ?_⟩
  funext g
  have h1 := congrFun hteq (fMap H H' hm' htop g)
  have hW' : @id (resLt (K := K) (K' := K') (LL := LL) hle T).V ((cW : ↥H → T.V) g) = (c'' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap H H' hm' htop g) := hW g
  have hκ'' : @id (resLt (K := K) (K' := K') (LL := LL) hle T).V ((cκ : ↥H → T.V) g) = (cκ' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap H H' hm' htop g) :=
    (hκ (fMap H H' hm' htop g)).symm
  change (resLt (K := K) (K' := K') (LL := LL) hle T).ρ ((fMap H H' hm' htop g : ↥H') : ↥(GK K')) t - t =
    @id (resLt (K := K) (K' := K') (LL := LL) hle T).V ((cW : ↥H → T.V) g) - n • @id (resLt (K := K) (K' := K') (LL := LL) hle T).V ((cκ : ↥H → T.V) g)
  rw [hW', hκ'']
  exact h1

end GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineBase

variable {l : ℕ} [Fact l.Prime]

def toTW {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL) (x : TW (RW LL) (resLt (K := K) (K' := K') (LL := LL) hle T)) : TW (RW LL) T := x

def Zf {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K))
    (c : ↥(latticeCocycles (resLat T H))) (b : TW (RW LL) T) (g : ↥H) : TW (RW LL) T :=
  (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥H → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ : ↥T.L.T) +
    (TWact (AI.gRW LL ((g : ↥(GK K)) : GQ l)) T (g : ↥(GK K)) b - b)

set_option maxHeartbeats 1000000 in
theorem push_cocycle {P : LocPrime l} (AI : LocAinf l P) {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL)
    (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K')) (hm : ∀ g : ↥H, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (htop : H' = ⊤) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H'))) : ∃ c : ↥(latticeCocycles (resLat T H)),
      (∀ g, (c : ↥H → T.V) g = (c' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap H H' hm htop g)) ∧
      ∀ (b : TW (RW LL) (resLt (K := K) (K' := K') (LL := LL) hle T)) g, Zf AI T H c (toTW hle T b) g = toTW hle T (Zf AI (resLt (K := K) (K' := K') (LL := LL) hle T) H' c' b (fMap H H' hm htop g)) :=
  ⟨⟨fun g => (c' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap H H' hm htop g),
    ⟨⟨c'.2.1.1.comp (fMap_cont H H' hm htop), fun g g' => c'.2.1.2 (fMap H H' hm htop g) (fMap H H' hm htop g')⟩,
      fun g _ => c'.2.2 _ trivial⟩⟩, fun _ => rfl, fun _ _ => rfl⟩

theorem toTW_φ {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL) (b : TW (RW LL) (resLt (K := K) (K' := K') (LL := LL) hle T)) :
    TWmap (φRW LL) T (toTW hle T b) - toTW hle T b = toTW hle T (TWmap (φRW LL) (resLt (K := K) (K' := K') (LL := LL) hle T) b - b) := rfl

theorem toTW_zero {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL) : toTW hle T 0 = 0 := rfl

set_option maxHeartbeats 1000000 in

theorem pull_h1f (P : LocPrime l) {K K' LL : FinExt l} (hle : K.1 ≤ K'.1) (T : Lt K LL)
    (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ H)
    (κ : LatticeCohomology (resLat T H)) (hκ : κ ∈ H1fSubmodule (P.PD K) H T) :
    ∃ (c : ↥(latticeCocycles (resLat T H))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H'))),
      (Submodule.Quotient.mk c : LatticeCohomology (resLat T H)) = κ ∧
      (Submodule.Quotient.mk c' : LatticeCohomology (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) H')) ∈ H1fSubmodule (P.PD K') H' (resLt (K := K) (K' := K') (LL := LL) hle T) ∧
      ∀ g, (c' : ↥H' → (resLt (K := K) (K' := K') (LL := LL) hle T).V) g = (c : ↥H → T.V) (eMap hle H H' hm g) :=
  hκ.elim fun c hc => hc.1.2.2.elim fun x hx => (pull_cocycle hle T H H' hm c).elim fun c' hc' =>
    ⟨c, c', hc.2, ⟨c', ⟨c'.2, c'.2.1, x, pull_f P hle T H H' hm _ _ hc' x hx⟩, rfl⟩, hc'⟩

set_option maxHeartbeats 2000000 in

theorem cl_fit (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T)
    (b : TW (RW LL) T) (hb : TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y) :
    ∃ c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)), Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
      (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) ∧
      ∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = ((HW l).W K s LL h).gam → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  refine (((F l).E K s LL h).tie.cl_def T ⟨(y, z), hyz⟩ b hb).elim fun c hc => ⟨c, hc.1, fun g hg => ?_, fun g hg => ?_⟩
  · have e := (hc.2 g ⟨_, GlobalTheory.HerrClassMaps.mem_T c g⟩ rfl).1 hg
    unfold Zf
    rw [e]
    exact neg_add_cancel _
  · have e := (hc.2 g ⟨_, GlobalTheory.HerrClassMaps.mem_T c g⟩ rfl).2 hg
    unfold Zf
    rw [e]
    exact sub_add_cancel _ _

set_option maxHeartbeats 1000000 in

theorem lam_exists (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    ∃ lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l], Continuous lam ∧
      (∀ g : ↥((HW l).W K s LL h).GKs, lam g = 1 ↔ ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) ∧
      (∀ g : ↥((HW l).W K s LL h).GKs, lam g = Multiplicative.ofAdd 1 ↔ ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = ((HW l).W K s LL h).gam) ∧
      (∃ g : ↥((HW l).W K s LL h).GKs, lam g = Multiplicative.ofAdd 1) ∧ IsClosed (((HW l).W K s LL h).GKs : Set ↥(GK K)) :=
  (GlobalTheory.HWL.Coord.exists_gamma_coordinates l (D.loc l) K s LL h (gamOf ((HW l).W K s LL h) ((HW l).W_s K s LL h))).1

def fHom {K K' : FinExt l} (H : Subgroup ↥(GK K)) (H' : Subgroup ↥(GK K'))
    (hm : ∀ g : ↥H, ((g : ↥(GK K)) : GQ l) ∈ GK K') (htop : H' = ⊤) : ↥H →* ↥H' where
  toFun := fMap H H' hm htop
  map_one' := rfl
  map_mul' := fun _ _ => rfl

end GlobalTheory.NL.CrystallineBase

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

section General

variable {R k : Type} [CommRing R] [CommRing k] {b a : ℕ}

open Classical in

theorem int_mul (O : Subring R) (ρ : O →+* k) (z : Matrix (Fin b) (Fin b) O) (y : Matrix (Fin a) (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, (z.map O.subtype * N * y.map O.subtype) i j ∈ O) ∧
    (Matrix.of fun i j => if h : (z.map O.subtype * N * y.map O.subtype) i j ∈ O then
        ρ ⟨(z.map O.subtype * N * y.map O.subtype) i j, h⟩ else 0) =
      z.map ρ * (Matrix.of fun i j => if h : N i j ∈ O then ρ ⟨N i j, h⟩ else 0) * y.map ρ := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix (Fin b) (Fin a) O, N = M.map O.subtype :=
    ⟨Matrix.of fun i j => ⟨N i j, h i j⟩, by ext i j; rfl⟩
  have key : z.map O.subtype * M.map O.subtype * y.map O.subtype = (z * M * y).map O.subtype := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have mem : ∀ i j, (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O := fun i j => by
    rw [key]; exact ((z * M * y) i j).2
  refine ⟨mem, ?_⟩
  have lhs : (Matrix.of fun i j => if h : (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O then
      ρ ⟨(z.map O.subtype * M.map O.subtype * y.map O.subtype) i j, h⟩ else 0) = (z * M * y).map ρ := by
    ext i j
    rw [Matrix.of_apply, dif_pos (mem i j), Matrix.map_apply]
    congr 1
    exact Subtype.ext (congrFun (congrFun key i) j)
  have mid : (Matrix.of fun i j => if h : M.map O.subtype i j ∈ O then ρ ⟨M.map O.subtype i j, h⟩ else 0) = M.map ρ := by
    ext i j
    rw [Matrix.of_apply, dif_pos (h i j)]
    rfl
  rw [lhs, mid, Matrix.map_mul, Matrix.map_mul]

theorem cancel (Z : GL (Fin b) R) (Y : GL (Fin a) R) (N : Matrix (Fin b) (Fin a) R) :
    Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val = N := by
  calc Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val
      = (Z.val * (Z⁻¹).val) * N * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem move {A : Type} [CommRing A] (f : A →+* R) (βS G Y : GL (Fin a) R) (βT H Z : GL (Fin b) R)
    (hY : βS * Y * βS⁻¹ = G) (hZ : βT * Z * βT⁻¹ = H)
    (g : Matrix (Fin a) (Fin a) A) (h : Matrix (Fin b) (Fin b) A) (hg : g.map f = G.val) (hh : h.map f = (H⁻¹).val)
    (x : Matrix (Fin b) (Fin a) A) :
    (βT⁻¹).val * (h * x * g).map f * βS.val = (Z⁻¹).val * ((βT⁻¹).val * x.map f * βS.val) * Y.val := by
  have eH : (H⁻¹).val = βT.val * ((Z⁻¹).val * (βT⁻¹).val) := by
    rw [← hZ, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  have eG : G.val = βS.val * (Y.val * (βS⁻¹).val) := by
    rw [← hY, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [Matrix.map_mul, Matrix.map_mul, hg, hh, eH, eG]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc (βT⁻¹).val βT.val, Units.inv_mul, Matrix.one_mul]

private theorem bc_mul_restrict_mul_bc_eq (O : Subring R) (ρ : O →+* k) (z : GL (Fin b) O) (y : GL (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, ((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O) ∧
    (Matrix.of fun i j => @dite _ (((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O)
        (Classical.propDecidable _) (fun h => ρ ⟨_, h⟩) (fun _ => 0)) =
      (Formalism.UG.bc ρ z).val *
        (Matrix.of fun i j => @dite _ (N i j ∈ O) (Classical.propDecidable _) (fun h => ρ ⟨N i j, h⟩) (fun _ => 0)) *
        (Formalism.UG.bc ρ y).val := by
  have ez : (Formalism.UG.bc O.subtype z).val = z.val.map O.subtype := rfl
  have ey : (Formalism.UG.bc O.subtype y).val = y.val.map O.subtype := rfl
  have ez' : (Formalism.UG.bc ρ z).val = z.val.map ρ := rfl
  have ey' : (Formalism.UG.bc ρ y).val = y.val.map ρ := rfl
  rw [ez, ey, ez', ey']
  exact GlobalTheory.FrameRed.int_mul O ρ z.val y.val N h

end General

variable {D : D7}

theorem isIntM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) :
    IsIntM (D := D) ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) ∧
    ∀ PP, redM (D := D) PP ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) =
      (Formalism.UG.bc (resS D.host.F PP) z).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  exact ⟨(bc_mul_restrict_mul_bc_eq _ (RingHom.id _) z y N h).1, fun PP => (bc_mul_restrict_mul_bc_eq _ (resS D.host.F PP) z y N h).2⟩

theorem mt_map (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (finE V g).val := rfl

theorem frMapO_actO {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {g : GA D S} {h : GA D T} {y : GL (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    {z : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : frGL βS y = finE S g) (hz : frGL βT z = finE T h) (x : WO S T) :
    frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) =
      ((intGL D.host.F D.host.E _ z)⁻¹).val * frMapO S T βS βT x * (intGL D.host.F D.host.E _ y).val := by
  have hY : βS * intGL D.host.F D.host.E _ y * βS⁻¹ = finE S g := by rw [← hy]; rfl
  have hZ : βT * intGL D.host.F D.host.E _ z * βT⁻¹ = finE T h := by rw [← hz]; rfl
  have hg : (Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) = (finE S g).val := by rw [inv_inv]; exact GlobalTheory.FrameRed.mt_map S g
  have hh : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((finE T h)⁻¹).val := by rw [GlobalTheory.FrameRed.mt_map, map_inv]
  show (βT⁻¹).val * (Formalism.L2.Theta.mt T h⁻¹ * x * Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) * βS.val = _
  exact GlobalTheory.FrameRed.move (toEAf D) βS (finE S g) (intGL D.host.F D.host.E _ y) βT (finE T h)
    (intGL D.host.F D.host.E _ z) hY hZ _ _ hg hh x

theorem isIntM_iff {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) :
    IsIntM (D := D) (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) ↔
      IsIntM (D := D) N := by
  constructor
  · intro hM
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z y⁻¹ hM).1
    rwa [map_inv (intGL D.host.F D.host.E a) y, GlobalTheory.FrameRed.cancel] at h1
  · intro hN
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y hN).1
    rwa [map_inv (intGL D.host.F D.host.E b) z] at h1

theorem redM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) (PP : Pl D.host.E) :
    redM (D := D) PP (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) =
      ((Formalism.UG.bc (resS D.host.F PP) z)⁻¹).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y h).2 PP
  rwa [map_inv (intGL D.host.F D.host.E b) z, map_inv (Formalism.UG.bc (resS D.host.F PP)) z] at h1

theorem frMapO_actO_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  intro D S T βS βT g h hg hh x
  unfold St at hg hh
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hg
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hh
  have e := GlobalTheory.FrameRed.frMapO_actO hy hz x
  refine ⟨?_, fun hI PP => ?_⟩
  · rw [e]
    exact GlobalTheory.FrameRed.isIntM_iff z y _
  · rw [e, GlobalTheory.FrameRed.redM_mul z y hI PP]
    have a : redFn βS PP (finE S g) = Formalism.UG.bc (resS D.host.F PP) y := by
      rw [← hy]; exact redFn_frGL βS PP y
    have b : redFn βT PP (finE T h) = Formalism.UG.bc (resS D.host.F PP) z := by
      rw [← hz]; exact redFn_frGL βT PP z
    rw [a, b]

end GlobalTheory.FrameRed

end

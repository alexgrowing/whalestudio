import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NtExpand

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace UpperTheory.V.Hi.LvR

section Abs

variable {l : ℕ} [Fact l.Prime] {F' F : W.GFrame l} (h : W.FHom F' F)

theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (W.GDet.ofRep ρ).comap φ = W.GDet.ofRep (ρ.comp φ) := by
  apply W.GDet.ext
  intro B _ _ y
  have key : ∀ z : MonoidAlgebra B H,
      W.GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ z) = W.GDet.repAlg (ρ.comp φ) B z := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | single g b => simp [W.GDet.repAlg, MonoidAlgebra.lift_single]
  exact congrArg Matrix.det (key y)

theorem chi_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G) (g : H) :
    (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  simp only [W.GDet.chi, W.GDet.comap, MonoidAlgebra.mapRingHom_single, map_one]
  show (D.D A[X]) (MonoidAlgebra.mapDomainRingHom A[X] φ _) = _
  rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]

theorem polar_comap (O : Type) [CommRing O] [Algebra ℤ_[l] O] {R : Type} [CommRing R] [Algebra O R] {n : ℕ}
    (D : W.GDet n R F.G₀) (hD : F.IsPolar O D) : F'.IsPolar O (D.comap h.π₀) := by
  intro B _ _ _ _ y
  have key : ∀ z : MonoidAlgebra B F'.G₀, MonoidAlgebra.mapDomainRingHom B h.π₀ (F'.star O B n z) =
      F.star O B n (MonoidAlgebra.mapDomainRingHom B h.π₀ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add, MulOpposite.unop_add] at *
      rw [ha, hb]
    | single g b =>
      have hc : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
        apply Subtype.ext
        show h.π (F'.c * (g : F'.Γ) * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
        rw [map_mul, map_mul, map_inv, h.hc]
      have he : F'.eps O B g = F.eps O B (h.π₀ g) := by
        apply Units.ext
        show (algebraMap O B) ((algebraMap ℤ_[l] O) (F'.ε g : ℤ_[l])) =
          (algebraMap O B) ((algebraMap ℤ_[l] O) (F.ε (h.π g) : ℤ_[l]))
        rw [h.hε]
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, hc, he]
  show D.D B (MonoidAlgebra.mapDomainRingHom B h.π₀ _) = D.D B (MonoidAlgebra.mapDomainRingHom B h.π₀ _)
  rw [key]
  exact hD B _

def upG {Lc : Pa.Loc} {G' G : Pa.Glob l Lc} (h : G'.Hom G) {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (h1 : ∀ i, IsOpen (((r.chib i).comp h.p₀).ker : Set G'.G₀))
    (h2 : Function.Injective fun i => (r.chib i).comp h.p₀)
    (h3 : G'.frame.IsPolar O (W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp h.p₀))) : Resid G'.frame O n :=
  ⟨fun i => (r.chib i).comp h.p₀, h1, h2, h3, r.psib, r.psib_open, r.th, r.th_comm⟩

theorem upG_compat {Lc : Pa.Loc} {G' G : Pa.Glob l Lc} (h : G'.Hom G) {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (h1 h2 h3) : Pa.Glob.Compat h (upG h r h1 h2 h3) r := ⟨fun _ => rfl, rfl, rfl⟩

end Abs

section Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

def fh : W.FHom V.frame V0.frame where
  π := h.p
  π_cont := h.cont
  hη := h.η
  hc := h.c
  hε := h.ε
  vl v := v
  gv _ := MonoidHom.id _
  gv_cont _ := continuous_id
  hφ v g := (h.φ v g).symm
  hI _ _ hg := hg

def p0 : V.frame.G₀ →* V0.frame.G₀ := (fh h).π₀

theorem continuous_levelChangeBaseGroupHom : Continuous (p0 h) := (h.cont.comp continuous_subtype_val).subtype_mk _

theorem surjective_levelChangeBaseGroupHom : Function.Surjective (p0 h) := by
  intro g
  obtain ⟨x, hx⟩ := h.surj (g : V0.frame.Γ)
  have hxk : V.η x = 1 := by
    have := h.η x
    rw [hx] at this
    exact this.symm.trans g.2
  exact ⟨⟨x, hxk⟩, Subtype.ext hx⟩

theorem levelChangeBaseGroupHom_apply_projection (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (g : G L Ω) : p0 h (V.pr g) = V0.pr g := Subtype.ext (hp _)

def rUp : Resid V.frame O n where
  chib i := (r.chib i).comp (p0 h)
  chib_open i := (r.chib_open i).preimage (continuous_levelChangeBaseGroupHom h)
  chib_inj i j e := r.chib_inj (MonoidHom.ext fun g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    exact DFunLike.congr_fun e x)
  polar := by
    have := polar_comap (fh h) O (W.GDet.ofRep (W.diagRep r.chib)) r.polar
    rw [ofRep_comap] at this
    exact this
  psib := r.psib
  psib_open := r.psib_open
  th v i := @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i)
  th_comm v i := @id (∀ g : W.muG l (Dec (F := L) (s.A v.1)), (g : Dec (F := L) (s.A v.1)) ∈
    (commutator (Dec (F := L) (s.A v.1))).topologicalClosure → @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) g = 1) (r.th_comm v i)

set_option maxHeartbeats 2000000 in
theorem psi_up {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (v : Vl l L) (i : Fin n) (ψ : Dec (F := L) (s.A v.1) →* Rˣ) :
    (rUp h).IsPsi v i ψ ↔ r.IsPsi v i ψ := by
  constructor
  · intro H
    have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
        ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
    exact ⟨H.cont, H.red, hm⟩
  · intro H
    have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
        ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
    exact ⟨H.cont, H.red, hm⟩

theorem rUp_Dbar : (rUp h).Dbar = r.Dbar.comap (p0 h) := by
  rw [Resid.Dbar, Resid.Dbar, ofRep_comap]; rfl

def rN : Resid (Pa.globOf r V).frame O n :=
  upG h (Pa.residOf r) (rUp h).chib_open (rUp h).chib_inj (rUp h).polar

theorem rN_compat : Pa.Glob.Compat h (rN h) (Pa.residOf r) := upG_compat _ _ _ _ _

theorem rN_Ip_le (u : s.St) (g : V.η.ker) (hg : g ∈ (rN h).Ip u) : g ∈ (rUp h).Ip u := by
  obtain ⟨⟨γ, ⟨h1, -⟩, rfl⟩, h2⟩ := hg
  exact ⟨⟨Subtype.val γ, h1, rfl⟩, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i⟩

theorem psi_N {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (v : Vl l L) (i : Fin n) (ψ : Dec (F := L) (s.A v.1) →* Rˣ)
    (H : (rUp h).IsPsi v i ψ) : (rN h).IsPsi v i ψ := by
  have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
      ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
  exact ⟨H.cont, H.red, hm⟩

def pairN {B : Type} [CommRing B] [Algebra O B] [Alg.IsCO O B] (u : Pair (rUp h) B) : Pair (rN h) B :=
  ⟨u.D, u.ψ, u.cont, u.red, fun v i => psi_N h v i _ (u.psi v i), u.P, u.Ord,
    fun w g hg => u.I w g (rN_Ip_le h w g hg)⟩

def lamUp (Λ : LamObj r) : LamObj (rUp h) where
  Λ := Λ.Λ
  κ := Λ.κ
  inert v i := by
    obtain ⟨ψ, hψ, e⟩ := Λ.inert v i
    exact ⟨ψ, (psi_up h v i ψ).2 hψ, e⟩
  univ R _ _ _ κ' hκ := Λ.univ R κ' fun v i => by
    obtain ⟨ψ, hψ, e⟩ := hκ v i
    exact ⟨ψ, (psi_up h v i ψ).1 hψ, e⟩

end Gen

end UpperTheory.V.Hi.LvR

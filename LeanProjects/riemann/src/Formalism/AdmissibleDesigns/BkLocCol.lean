import Formalism.AdmissibleDesigns.LengthSemilinear
import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointCondH0W

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf

section Col

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem bkLoc_col (n : ℕ) (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρV : Representation (D.nd.O i) ↥(decs D.host.E (Aw i dc) n) V) (qV : V →ₗ[D.nd.O i] M)
    (Ψ : TrV (eK (D.nbr i _ hw)) V →ₗ[Br.LLw (D.nbr i _ hw)] (Fin D.R.r → Br.LLw (D.nbr i _ hw)))
    (hΨc : Continuous Ψ)
    (hΨe : ∀ g v, Ψ (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw) g v) =
      matRep (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g (Ψ v))
    (hcomp : ∀ v, Br.phi (D.nbr i _ hw) D.R.r (φ (qV v)) = Submodule.Quotient.mk (Ψ v))
    (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))))
    (hy : psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈
      F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV) :
    y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π) := by
  induction y using Submodule.Quotient.induction_on with
  | H f =>
    have hy' : Submodule.Quotient.mk (psiZ (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) f) ∈
        F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV := hy
    obtain ⟨c, hc, hceq⟩ := Submodule.mem_map.mp hy'
    have hd := (Submodule.Quotient.eq _).1 hceq
    have hpsi := Submodule.sub_mem _ hc (Submodule.mem_sup_right hd)
    simp only [Submodule.mem_comap, Submodule.coe_subtype, sub_sub_cancel] at hpsi
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hpsi
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨m, rfl⟩ := hb
    have hz' : z ∈ fZ i dc n ρV := hz
    unfold fZ at hz'
    rw [dif_pos hw] at hz'
    have hz2 : (fun g => (z (Br.iota D.nbr i _ hw g) : TrV (eK (D.nbr i _ hw)) V)) ∈
        finiteCocycles (Br.PD D.loc D.nbr i _ hw) (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw)) := hz'
    have hpt : ∀ x, f.1 x = φ (qV (z x)) + ((Br.WKO i ρ π) (x : GE D.nd) (φ m) - φ m) := by
      intro x
      have e := congrFun hab x
      change qV (z x) + (uRep (D.nd.O i) (M := M) r χ (x : GE D.nd) m - m) = φ.symm (f.1 x) at e
      rw [← hφ, ← map_sub, ← map_add, e, LinearEquiv.apply_symm_apply]
    have h1 : (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_left ⟨fun g => Ψ (z (Br.iota D.nbr i _ hw g)),
        (cocyclesFunctorial_holds _ _ _ _ _ _ _ _ _ _ _ _ Ψ hΨc hΨe _).2 hz2, rfl⟩
    have h2 : (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_right ⟨Br.phi (D.nbr i _ hw) D.R.r (φ m), rfl⟩
    have h3 := Submodule.add_mem _ h1 h2
    have hfun : (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) f :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) =
        (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g)))) +
        (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) := by
      funext g
      have hact : Br.phi (D.nbr i _ hw) D.R.r (Br.WKO i ρ π (Br.ι (D.nbr i _ hw) g : GE D.nd) (φ m)) =
          actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
            (Br.phi (D.nbr i _ hw) D.R.r (φ m)) :=
        phi_act D i (plOf i dc n) hw ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))) g (φ m)
      show Br.phi (D.nbr i _ hw) D.R.r (f.1 (Br.ι (D.nbr i _ hw) g)) = _
      rw [hpt, map_add, map_sub, hcomp]
      exact congrArg (fun t => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) +
        (t - Br.phi (D.nbr i _ hw) D.R.r (φ m))) hact
    have hmem : f ∈ (HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
        (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))))).comap
          (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))) := by
      exact Submodule.mem_comap.mpr (hfun ▸ h3)
    exact ⟨f, hmem, rfl⟩

def BkRow (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ n ∈ rowsN i dc,
    ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
      (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))),
      psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
          ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈ F n →
        y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π)

end Col

end Formalism.MainNotions.N.K.Sel

end

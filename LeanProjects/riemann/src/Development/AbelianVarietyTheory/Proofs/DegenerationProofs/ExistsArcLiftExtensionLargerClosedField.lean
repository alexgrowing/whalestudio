import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtensionStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.LiftExt
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Field F']
    [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] [Algebra (FractionRing R) F'']
    {f : F →+* F'} {f' : F' →+* F''} {k : ℕ} {p : QkPt D F k} {p' : QkPt D F' k} {p'' : QkPt D F'' k}
    (h : QkExt f p p') (h' : QkExt f' p' p'') : QkExt (f'.comp f) p p'' := by
  have e : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp' f f'
  refine ⟨h'.1.trans h.1, by rw [h'.2.1, h.2.1, e, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

theorem equiv_of_base {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p₀ : QkPt D (FractionRing R) k} {r : QkPt D F k}
    (h : ∀ p, QkExt (algebraMap (FractionRing R) F) p₀ p → QkPt.Equiv D F p r) (p' : QkPt D F' k)
    (hp' : QkExt (algebraMap (FractionRing R) F') p₀ p') : QkPt.Equiv D F' p' (qkExt hB f hf r) := by
  obtain ⟨p, hp, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing R) F) (RingHom.ext fun _ => rfl) p₀
  have h₁ := qkExt_trans hp ((qkExt_iff hB f hf p _).2 rfl)
  rw [hf] at h₁
  rw [(existsUnique_qkExt hB (algebraMap (FractionRing R) F') (RingHom.ext fun _ => rfl) p₀).unique hp' h₁]
  exact qkExt_congr hB f hf (h p hp)

theorem exists_lift_ext : Laws → BrGtSt → BrWpSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing O') F'] (f : F →+* F'), f.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' → ∀ S : ValuationSubring F', (∀ r : O', algebraMap (FractionRing O') F' (algebraMap O' _ r) ∈ S) → ∀ A : Lift a F, ∃ A' : Lift a F', A'.ν.Integral S ∧ ∃ I : NumD.Hom f A.N A'.N, I.lam = 1 ∧ f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧ (∀ y, A'.ν.eX (I.e y) = A.ν.eX y) ∧ ∀ n v, (A'.q n v).1.1.toAdd = I.e (A.q n v).1.1.toAdd ∧ I.Rel (A.q n v).1.2 (A'.q n v).1.2 := by
  intro hL hGt hWp E _ _ _ H D l Xo c W₀ Y R _ _ _ b ϖ a _ F F' _ _ _ _ _ _ f hf S hS A
  have hf₀ : ∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x := fun x =>
    DFunLike.congr_fun hf x
  have : CharZero F := charZero_of_isPrimitiveRoot A.I.ζ_prim
  obtain ⟨J', hg, hJ⟩ := GlobalTheory.ValuesExist.exists_gauge F' S a.D₀.P.isLB
  obtain ⟨N', ν', rfl, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R a.D₀ a.even a.bimult F' J' hg A.ν.th A.ν.th_gen
  have G := (hGt R a.D₀ a.even a.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R a.D₀ a.even a.bimult F' N' ν').2.2.2.2
  obtain ⟨I, hlam, heX, hI⟩ := GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension R a.D₀ F F' f hf A.N N' A.ν ν' hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt a.D₀ F k) (z : F), WeilQkIs a.D₀ F k p p' z →
      WeilQkIs a.D₀ F' k (qkExt a.bimult f hf p) (qkExt a.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt a.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt a.bimult f hf p')
    have e := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq hr
    have e' := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq' hr'
    rw [hWp R a.D₀ a.even a.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' e.1 e.2 e'.1 e'.2,
      (hWp R a.D₀ a.even a.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (v : D.La) => ((G' n).1 (qkExt a.bimult f hf (A.I.ev n v))).exists
  refine ⟨{ ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf a.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq'
            be := { be := a.be.compl₁₂ ν'.eX.toAddMonoidHom.toIntLinearMap ν'.eX.toAddMonoidHom.toIntLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ fun h => hy (ν'.eX.map_eq_zero_iff.1 h)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r hr => (congrArg f (A.ρ_eq r hr)).trans (hf₀ _)
            ζ_eq := fun z hz => (congrArg f (A.ζ_eq z hz)).trans (hf₀ _)
            levA := fun v => equiv_of_base a.bimult f hf (A.levA v)
            levM := fun v hv => equiv_of_base a.bimult f hf (A.levM v hv)
            closed := inferInstance },
    fun x => hJ _ (GlobalTheory.ValuesExist.exists_ext a.D₀ F' S hS x), I, hlam, rfl, fun _ _ => rfl, heX,
    fun n v => hI n _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) (A.hq n v) (hq' n v)⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
  obtain ⟨n, h₁, h₂⟩ := A.det τ
  have := a.D₀.P.isAb.smooth
  refine ⟨n, ?_, h₂.trans (by
    by_cases h : τ H.rt = A.ρ
    · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
    · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
  have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
      spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
    rw [← spMap_comp', ← RingHom.comp_assoc, hf]
  rw [e]
  exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁

end GlobalTheory.LiftExt
end

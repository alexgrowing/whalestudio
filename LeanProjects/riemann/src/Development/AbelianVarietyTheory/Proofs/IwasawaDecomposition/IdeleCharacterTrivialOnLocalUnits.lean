import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoOfForallIntegral

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.LocTriv

variable {L : Type} [Field L] [NumberField L]

theorem tendsto_finiteAdele {ι : Type} {l : Filter ι} (f : ι → FiniteAdeleRing (𝓞 L) L) (b : FiniteAdeleRing (𝓞 L) L)
    (hf : ∀ i v, f i v ∈ v.adicCompletionIntegers L) (hb : ∀ v, b v ∈ v.adicCompletionIntegers L)
    (h : ∀ v, Tendsto (fun i => f i v) l (𝓝 (b v))) : Tendsto f l (𝓝 b) := by
  first
  | exact @_root_.GlobalTheory.TendstoOfIntegrals.target_check
  | exact _root_.GlobalTheory.TendstoOfIntegrals.target_check
  | (apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TendstoOfIntegrals.target_check <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TendstoOfIntegrals.target_check ..)

def ev (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def part (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  ∏ v ∈ S, localIdele L v (Units.map (ev v) a)

theorem part_inv (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S)⁻¹ = part a⁻¹ S := by
  simp only [part, map_inv, Finset.prod_inv_distrib]

theorem ev_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ev v (localIdele L v x : AdeleRing (𝓞 L) L) = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_local_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ev w (localIdele L v x : AdeleRing (𝓞 L) L) = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_part_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) :
    ev w (part a S : AdeleRing (𝓞 L) L) = ev w (a : AdeleRing (𝓞 L) L) := by
  rw [part, Units.coe_prod, map_prod, Finset.prod_eq_single_of_mem w hw (fun v _ hv => ev_local_ne hv.symm _),
    ev_local_self]
  rfl

theorem ev_part_not_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ S) : ev w (part a S : AdeleRing (𝓞 L) L) = 1 := by
  rw [part, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun v hv => ev_local_ne (fun e : w = v => hw (e ▸ hv)) _

theorem part_fst (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S : AdeleRing (𝓞 L) L).1 = 1 := by
  have h : finPartI L (part a S) = part a S := by
    rw [part, map_prod]
    exact Finset.prod_congr rfl fun v _ => Units.ext rfl
  rw [← h]
  rfl

theorem tendsto_part_val {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : (a : AdeleRing (𝓞 L) L).1 = 1) :
    Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L)) atTop (𝓝 (a : AdeleRing (𝓞 L) L)) := by
  have h2 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).2) atTop (𝓝 (a : AdeleRing (𝓞 L) L).2) := by
    refine tendsto_finiteAdele _ _ (fun S v => ?_) (fun v => (ha v).le) fun v => ?_
    · show ev v (part a S : AdeleRing (𝓞 L) L) ∈ _
      by_cases hv : v ∈ S
      · rw [ev_part_mem a hv]
        exact (ha v).le
      · rw [ev_part_not_mem a hv]
        exact one_mem _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({v} : Finset _)] with S hS
      exact (ev_part_mem a (hS (Finset.mem_singleton_self v))).symm
  have h3 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).1) atTop (𝓝 (a : AdeleRing (𝓞 L) L).1) := by
    rw [h1]
    exact tendsto_const_nhds.congr fun S => (part_fst a S).symm
  exact h3.prodMk_nhds h2

theorem tendsto_part {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : ∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    Tendsto (part a) atTop (𝓝 a) := by
  have e : finPartI L a = a := finPartI_eq_self h1
  have e' : finPartI L a⁻¹ = a⁻¹ := by rw [map_inv, e]
  have t1 := tendsto_part_val ha (by rw [← e]; rfl)
  have t2 := tendsto_part_val ((unitIdl L).inv_mem ha) (by rw [← e']; rfl)
  simp only [← part_inv] at t2
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp t2)

open Classical in

theorem eq_one_of_local : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  intro L _ _ ψ hψ a ha h1 hl
  have t := (hψ.tendsto a).comp (tendsto_part ha h1)
  have e : ψ ∘ part a = fun _ => 1 := funext fun S => by
    show ψ (part a S) = 1
    rw [part, map_prod]
    exact Finset.prod_eq_one fun v _ => hl v _ rfl
  rw [e] at t
  exact tendsto_nhds_unique t tendsto_const_nhds

end GlobalTheory.Mem.LocTriv

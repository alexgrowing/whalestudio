import Formalism.LocalToGlobal.Columns.TiedUpDnLoc

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Kv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def mhlKv (v : HeightOneSpectrum (𝓞 F)) : Subgroup (UAd hc n) where
  carrier := {η | (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
    bc (prV (E := E) v) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))}
  one_mem' := ⟨fun w _ => by rw [OneMemClass.coe_one, map_one], by rw [OneMemClass.coe_one, map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Subgroup.coe_mul, map_mul, ha1 w hw, hb1 w hw, mul_one]
    · rw [Subgroup.coe_mul, map_mul]; exact mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [InvMemClass.coe_inv, map_inv, ha1 w hw, inv_one]
    · rw [InvMemClass.coe_inv, map_inv]; exact inv_mem ha2

variable {hc n}

theorem mem_mhlKv_iff {v : HeightOneSpectrum (𝓞 F)} {η : UAd hc n} :
    η ∈ mhlKv hc n v ↔ (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
    bc (prV (E := E) v) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) :=
  Iff.rfl

theorem mhl_eq_put {v : HeightOneSpectrum (𝓞 F)} {η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hη : η ∈ UAd hc n)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) η = 1) :
    η = rll_put n v (bc (prV (E := E) v) η) := by
  have h1 : (afsplitE hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩).2 = 1 :=
    (afsplitE_snd_eq_one hc.sig 1 v ⟨η, hη⟩).2 h
  have h2 : afsplitU v 1 η = 1 := by
    rw [← afsplitE_snd hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩]
    exact congrArg Subtype.val h1
  conv_lhs => rw [← afsplit_left v η, h2]
  rfl

variable (ST SG : Finset (Pl E))

theorem put_mem_kOne_of_not_over {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {g : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hU : rll_put n v g ∈ UAd hc n)
    (hg : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : rll_put n v g ∈ K1 hc n ST SG := by
  have hS := rll_put_mem_St n v hg
  have hJ : rll_put n v g ∈ J0 hc n ST := by
    refine ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_⟩
    refine ⟨⟨rll_put n v g, hS⟩, ?_, rfl⟩
    show redAt 1 P ⟨rll_put n v g, hS⟩ ∈ mirab (kP P) n
    rw [rll_put_red n v g hS P (hST P hP)]
    exact one_mem _
  refine ⟨⟨_, hJ⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
  funext w
  exact rll_put_red n v g hS w.1 (hSG w.1 w.2)

theorem localLevel_le_kOne {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {η : UAd hc n} (hη : η ∈ mhlKv hc n v) : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG := by
  have e := mhl_eq_put η.2 hη.1
  rw [e] at ⊢
  exact put_mem_kOne_of_not_over ST SG hST hSG (e ▸ η.2) hη.2

theorem decoOf_mul_mhlKv {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {η : UAd hc n} (hη : η ∈ mhlKv hc n v) :
    decoOf ST SG (x * (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) = decoOf ST SG x :=
  decoration_mul_principal hc n ST SG x (localLevel_le_kOne ST SG hST hSG hη)

theorem mem_localLevel_of_mem_kOne {v : HeightOneSpectrum (𝓞 F)} {η : UAd hc n}
    (h1 : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hK : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG) : η ∈ mhlKv hc n v := by
  refine ⟨h1, ?_⟩
  have hS : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hK)
  rw [St_one] at hS
  exact Formalism.L2.DIV.lc_stab_loc v (stdLat E n) _ hS

theorem mhl_inv_mul_mem {v : HeightOneSpectrum (𝓞 F)} (x g g' : UAd hc n)
    (hg : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hg' : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (h : decoOf ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoOf ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    g⁻¹ * g' ∈ mhlKv hc n v := by
  have hr : decoRaw ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoRaw ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← rlc_decoOf_val hc n ST SG (x * g).2, ← rlc_decoOf_val hc n ST SG (x * g').2, h]
  have hK := mem_principal_of_same_decoration hc n ST SG (x * g).2 (x * g').2 hr
  have e : ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * ((x * g' : UAd hc n) : GL (Fin n) _) =
      ((g⁻¹ * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  rw [e] at hK
  refine mem_localLevel_of_mem_kOne ST SG (fun w hw => ?_) hK
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, hg w hw, hg' w hw, inv_one, one_mul]

end Kv

end Formalism.L2.Col

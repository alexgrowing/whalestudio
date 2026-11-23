import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.IdeleClass

variable (E : Type) [Field E] [NumberField E]

theorem localIdele_snd_self' (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion E)

theorem localIdele_snd_ne' (v w : HeightOneSpectrum (𝓞 E)) (h : w ≠ v) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)

theorem classHom_val (a : Ideles E) :
    ((((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) := rfl

theorem finIdele_apply (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.Mem.UnitIndex.finIdele E a : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v =
      (a : AdeleRing (𝓞 E) E).2 v := rfl

theorem classHom_eq_one_of_mem_unitIdl {a : Ideles E} (ha : a ∈ GlobalTheory.Mem.Chr.unitIdl E) :
    GlobalTheory.Mem.UnitIndex.classHom E a = 1 := by
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq]
    exact (GlobalTheory.Idele.smul_eq_self_iff _ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).2 fun v => ha v
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a = 1 :=
    Units.ext (by rw [classHom_val, h]; rfl)
  show ClassGroup.mk E _ = 1
  rw [hu, map_one]

theorem unitIdl_le_ker : GlobalTheory.Mem.Chr.unitIdl E ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker :=
  fun _ ha => classHom_eq_one_of_mem_unitIdl E ha

theorem infConn_le_unitIdl : infConn E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  rintro _ ⟨y, -, rfl⟩ v
  show Valued.v (1 : v.adicCompletion E) = 1
  exact map_one _

theorem diagUnits_range_le_ker : (diagUnits E).range ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker := by
  rintro _ ⟨k, rfl⟩
  have hd : GlobalTheory.Mem.UnitIndex.finIdele E (diagUnits E k) =
      FiniteAdeleRing.unitEmbedding (𝓞 E) E k := Units.ext rfl
  show ClassGroup.mk E _ = 1
  rw [ClassGroup.mk_eq_one_iff, classHom_val, hd, GlobalTheory.Idele.idealOf_unitEmbedding,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(k : E), rfl⟩⟩

theorem localIdele_mem_unitIdl (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnitAt v x) : localIdele E v x ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self']
    exact hx
  · rw [localIdele_snd_ne' E v w hw]
    exact map_one _

open Classical in
theorem ord_vw_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) w =
      if v = w then 1 else 0 := by
  rw [GlobalTheory.Idele.ord_vw, finIdele_apply]
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self', if_pos rfl]
    have hx' : Valued.v (x : w.adicCompletion E) = WithZero.exp (-1) := hx
    rw [hx', WithZero.log_exp]
    rfl
  · rw [localIdele_snd_ne' E v w hw, if_neg (Ne.symm hw), map_one]
    rfl

theorem classHom_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) :
    GlobalTheory.Mem.UnitIndex.classHom E (localIdele E v x) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  classical
  have hv : ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := by simpa using v.ne_bot
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) =
      (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) := by
    refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) hv fun w => ?_
    rw [GlobalTheory.Idele.count_idealOf, ord_vw_localIdele_unif E v x hx w,
      FractionalIdeal.count_maximal]
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits
      (localIdele E v x) =
      FractionalIdeal.mk0 E ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
    Units.ext (by rw [classHom_val, h, FractionalIdeal.coe_mk0])
  show ClassGroup.mk E _ = _
  rw [hu, ClassGroup.mk_mk0]

end GlobalTheory.IdeleClass

namespace GlobalTheory

theorem exists_ideleClassHom : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro E _ _
  refine ⟨GlobalTheory.Mem.UnitIndex.classHom E,
    Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl,
    sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E)
      ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleClass.unitIdl_le_ker E)),
    fun v x hx => GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E
      (GlobalTheory.IdeleClass.localIdele_mem_unitIdl E v x hx),
    fun v x hx => GlobalTheory.IdeleClass.classHom_localIdele_unif E v x hx⟩

end GlobalTheory
